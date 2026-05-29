theory Pcre_POC
  imports Main
begin

section \<open>PCRE-style operational proof-of-concept\<close>

text \<open>
  This theory is a deliberately small semantic kernel for PCRE-style engine
  behaviour.  It does not replace the POSIX development.  Instead it isolates
  the operational phenomena that are awkward for a pure regular-language
  account: ordered backtracking, greedy and lazy quantifier order,
  possessive/non-backtracking commitment, atomic groups, captures,
  backreferences, anchors, and zero-width lookaround.

  The matcher is fuelled.  Fuel is a proof-engineering device and also models
  the production-engine obligation to bound recursive exploration.  Repeated
  bodies must make strict input progress, which is the standard guard against
  nullable-loop divergence in practical engines.
\<close>

datatype qkind = Greedy | Lazy | Possessive | Linear

type_synonym capenv = "nat \<Rightarrow> string option"

datatype pstate =
  PState (pleft: string) (pright: string) (pcaps: capenv)

datatype pcre_result =
  PResult (rstart: nat) (rend: nat) (rcaps: capenv)

datatype pcre =
  PFail
| PEps
| PChar char
| PClass "char set"
| PDot "char set"
| PSeq pcre pcre
| PAlt pcre pcre
| PQuant qkind nat "nat option" pcre
| PCapture nat pcre
| PBackref nat
| PAtomic pcre
| PLook bool pcre
| PLookBehind bool pcre
| PCond nat pcre pcre
| PWordBoundary "char set" bool
| PLineStart "char set"
| PLineEnd "char set"
| PStart
| PEnd

definition empty_caps :: capenv
where
  "empty_caps = (\<lambda>_. None)"

definition starts_with :: "string \<Rightarrow> string \<Rightarrow> bool"
where
  "starts_with p s \<longleftrightarrow> take (length p) s = p"

lemma starts_with_drop:
  assumes "starts_with p s"
  shows "s = p @ drop (length p) s"
  using assms append_take_drop_id[of "length p" s]
  by (simp add: starts_with_def)

fun can_take :: "nat option \<Rightarrow> bool"
where
  "can_take None = True"
| "can_take (Some n) = (0 < n)"

fun dec_bound :: "nat option \<Rightarrow> nat option"
where
  "dec_bound None = None"
| "dec_bound (Some 0) = Some 0"
| "dec_bound (Some (Suc n)) = Some n"

fun first_only :: "'a list \<Rightarrow> 'a list"
where
  "first_only [] = []"
| "first_only (x # xs) = [x]"

fun splits :: "'a list \<Rightarrow> ('a list * 'a list) list"
where
  "splits [] = [([], [])]"
| "splits (x # xs) = ([], x # xs) # map (\<lambda>(p, s). (x # p, s)) (splits xs)"

fun last_opt :: "'a list \<Rightarrow> 'a option"
where
  "last_opt [] = None"
| "last_opt [x] = Some x"
| "last_opt (x # y # xs) = last_opt (y # xs)"

definition option_in :: "'a set \<Rightarrow> 'a option \<Rightarrow> bool"
where
  "option_in A x = (case x of None \<Rightarrow> False | Some c \<Rightarrow> c \<in> A)"

definition word_boundary :: "char set \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool"
where
  "word_boundary W l r \<longleftrightarrow>
    option_in W (last_opt l) \<noteq> option_in W (case r of [] \<Rightarrow> None | c # s \<Rightarrow> Some c)"

definition line_start :: "char set \<Rightarrow> string \<Rightarrow> bool"
where
  "line_start NL l \<longleftrightarrow> l = [] \<or> option_in NL (last_opt l)"

definition line_end :: "char set \<Rightarrow> string \<Rightarrow> bool"
where
  "line_end NL r \<longleftrightarrow> r = [] \<or> option_in NL (case r of [] \<Rightarrow> None | c # s \<Rightarrow> Some c)"

fun first_nonempty_map :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "first_nonempty_map f [] = []"
| "first_nonempty_map f (x # xs) =
    (let ys = f x in if ys = [] then first_nonempty_map f xs else ys)"

definition consumes_prefix :: "pstate \<Rightarrow> pstate \<Rightarrow> bool"
where
  "consumes_prefix st st' \<longleftrightarrow>
    (\<exists>w. pleft st' = pleft st @ w \<and> pright st = w @ pright st')"

definition consumes_strict :: "pstate \<Rightarrow> pstate \<Rightarrow> bool"
where
  "consumes_strict st st' \<longleftrightarrow> length (pright st') < length (pright st)"

definition progress_outputs :: "pstate \<Rightarrow> pstate list \<Rightarrow> pstate list"
where
  "progress_outputs st xs = filter (consumes_strict st) xs"

definition capture_update :: "nat \<Rightarrow> string \<Rightarrow> pstate \<Rightarrow> pstate"
where
  "capture_update n l0 st =
    (case st of PState l r caps \<Rightarrow> PState l r (caps(n := Some (drop (length l0) l))))"

definition is_substring :: "string \<Rightarrow> string \<Rightarrow> bool"
where
  "is_substring w s \<longleftrightarrow> (\<exists>pre post. s = pre @ w @ post)"

definition valid_caps :: "string \<Rightarrow> capenv \<Rightarrow> bool"
where
  "valid_caps subject caps \<longleftrightarrow> (\<forall>n w. caps n = Some w \<longrightarrow> is_substring w subject)"

fun pmatch :: "nat \<Rightarrow> pcre \<Rightarrow> pstate \<Rightarrow> pstate list"
and qmatch :: "nat \<Rightarrow> qkind \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> pcre \<Rightarrow> pstate \<Rightarrow> pstate list"
where
  "pmatch 0 r st = []"
| "pmatch (Suc fuel) PFail st = []"
| "pmatch (Suc fuel) PEps st = [st]"
| "pmatch (Suc fuel) (PChar c) (PState l [] caps) = []"
| "pmatch (Suc fuel) (PChar c) (PState l (d # s) caps) =
    (if c = d then [PState (l @ [d]) s caps] else [])"
| "pmatch (Suc fuel) (PClass C) (PState l [] caps) = []"
| "pmatch (Suc fuel) (PClass C) (PState l (d # s) caps) =
    (if d \<in> C then [PState (l @ [d]) s caps] else [])"
| "pmatch (Suc fuel) (PDot excluded) (PState l [] caps) = []"
| "pmatch (Suc fuel) (PDot excluded) (PState l (d # s) caps) =
    (if d \<notin> excluded then [PState (l @ [d]) s caps] else [])"
| "pmatch (Suc fuel) (PSeq r1 r2) st =
    concat (map (pmatch fuel r2) (pmatch fuel r1 st))"
| "pmatch (Suc fuel) (PAlt r1 r2) st =
    pmatch fuel r1 st @ pmatch fuel r2 st"
| "pmatch (Suc fuel) (PQuant q lo hi r) st =
    qmatch fuel q lo hi r st"
| "pmatch (Suc fuel) (PCapture n r) (PState l s caps) =
    map (capture_update n l) (pmatch fuel r (PState l s caps))"
| "pmatch (Suc fuel) (PBackref n) (PState l s caps) =
    (case caps n of
      None \<Rightarrow> []
    | Some w \<Rightarrow>
        (if starts_with w s then [PState (l @ w) (drop (length w) s) caps] else []))"
| "pmatch (Suc fuel) (PAtomic r) st =
    first_only (pmatch fuel r st)"
| "pmatch (Suc fuel) (PLook positive r) st =
    (if (positive \<and> pmatch fuel r st \<noteq> []) \<or>
        (\<not> positive \<and> pmatch fuel r st = [])
     then [st] else [])"
| "pmatch (Suc fuel) (PLookBehind positive r) (PState l s caps) =
    (let ok =
      (\<exists>pre suf out.
        (pre, suf) \<in> set (splits l) \<and>
        out \<in> set (pmatch fuel r (PState pre suf caps)) \<and>
        pleft out = l \<and> pright out = [])
     in if (positive \<and> ok) \<or> (\<not> positive \<and> \<not> ok)
        then [PState l s caps] else [])"
| "pmatch (Suc fuel) (PCond n yes no) st =
    (if pcaps st n = None then pmatch fuel no st else pmatch fuel yes st)"
| "pmatch (Suc fuel) (PWordBoundary W positive) (PState l s caps) =
    (if word_boundary W l s = positive then [PState l s caps] else [])"
| "pmatch (Suc fuel) (PLineStart NL) (PState l s caps) =
    (if line_start NL l then [PState l s caps] else [])"
| "pmatch (Suc fuel) (PLineEnd NL) (PState l s caps) =
    (if line_end NL s then [PState l s caps] else [])"
| "pmatch (Suc fuel) PStart (PState l s caps) =
    (if l = [] then [PState l s caps] else [])"
| "pmatch (Suc fuel) PEnd (PState l s caps) =
    (if s = [] then [PState l s caps] else [])"
| "qmatch 0 q lo hi r st = []"
| "qmatch (Suc fuel) q lo hi r st =
    (if 0 < lo then
       (if can_take hi
        then concat
          (map (qmatch fuel q (lo - 1) (dec_bound hi) r)
            (progress_outputs st (pmatch fuel r st)))
        else [])
     else if can_take hi then
       (let next = progress_outputs st (pmatch fuel r st);
            more = concat (map (qmatch fuel q 0 (dec_bound hi) r) next)
        in case q of
          Greedy \<Rightarrow> more @ [st]
        | Lazy \<Rightarrow> st # more
        | Possessive \<Rightarrow>
            (case next of
              [] \<Rightarrow> [st]
            | st1 # rest \<Rightarrow> qmatch fuel Possessive 0 (dec_bound hi) r st1)
        | Linear \<Rightarrow>
            (case next of
              [] \<Rightarrow> [st]
            | st1 # rest \<Rightarrow> qmatch fuel Linear 0 (dec_bound hi) r st1))
     else [st])"

definition pcre_fullmatch :: "nat \<Rightarrow> pcre \<Rightarrow> string \<Rightarrow> bool"
where
  "pcre_fullmatch fuel r s \<longleftrightarrow>
    (\<exists>st' \<in> set (pmatch fuel r (PState [] s empty_caps)). pright st' = [])"

definition pcre_fullmatch_language :: "nat \<Rightarrow> pcre \<Rightarrow> string set"
where
  "pcre_fullmatch_language fuel r = {s. pcre_fullmatch fuel r s}"

definition pcre_search_states :: "nat \<Rightarrow> pcre \<Rightarrow> string \<Rightarrow> pstate list"
where
  "pcre_search_states fuel r s =
    first_nonempty_map
      (\<lambda>i. pmatch fuel r (PState (take i s) (drop i s) empty_caps))
      [0..<Suc (length s)]"

definition pcre_search :: "nat \<Rightarrow> pcre \<Rightarrow> string \<Rightarrow> bool"
where
  "pcre_search fuel r s \<longleftrightarrow> pcre_search_states fuel r s \<noteq> []"

definition pcre_search_entries :: "nat \<Rightarrow> pcre \<Rightarrow> string \<Rightarrow> (nat * pstate) list"
where
  "pcre_search_entries fuel r s =
    first_nonempty_map
      (\<lambda>i. map (\<lambda>out. (i, out))
        (pmatch fuel r (PState (take i s) (drop i s) empty_caps)))
      [0..<Suc (length s)]"

definition result_of_entry :: "nat * pstate \<Rightarrow> pcre_result"
where
  "result_of_entry entry =
    (case entry of (i, PState l rest caps) \<Rightarrow> PResult i (length l) caps)"

definition pcre_exec :: "nat \<Rightarrow> pcre \<Rightarrow> string \<Rightarrow> pcre_result option"
where
  "pcre_exec fuel r s =
    (case pcre_search_entries fuel r s of
      [] \<Rightarrow> None
    | entry # rest \<Rightarrow> Some (result_of_entry entry))"

lemma consumes_prefix_refl [simp]:
  "consumes_prefix st st"
  by (cases st) (auto simp add: consumes_prefix_def)

lemma consumes_prefix_trans:
  assumes "consumes_prefix st st1" "consumes_prefix st1 st2"
  shows "consumes_prefix st st2"
  using assms
  by (cases st; cases st1; cases st2)
     (auto simp add: consumes_prefix_def append_assoc)

lemma consumes_prefix_backref:
  assumes "starts_with w s"
  shows "consumes_prefix (PState l s caps) (PState (l @ w) (drop (length w) s) caps)"
  using starts_with_drop[OF assms]
  by (auto simp add: consumes_prefix_def append_assoc)

lemma capture_update_consumes_prefix [simp]:
  "consumes_prefix st (capture_update n l0 st') \<longleftrightarrow> consumes_prefix st st'"
  by (cases st; cases st') (simp add: capture_update_def consumes_prefix_def)

lemma first_only_subset:
  "x \<in> set (first_only xs) \<Longrightarrow> x \<in> set xs"
  by (cases xs) auto

lemma first_only_length_le_one:
  "length (first_only xs) \<le> 1"
  by (cases xs) auto

lemma first_only_member_head:
  assumes "x \<in> set (first_only xs)"
  shows "\<exists>rest. xs = x # rest"
proof (cases xs)
  case Nil
  then show ?thesis using assms by simp
next
  case (Cons y rest)
  then have "x = y" using assms by simp
  then have "xs = x # rest" using Cons by simp
  then show ?thesis ..
qed

lemma progress_outputs_subset:
  "x \<in> set (progress_outputs st xs) \<Longrightarrow> x \<in> set xs"
  by (auto simp add: progress_outputs_def)

lemma empty_caps_valid [simp]:
  "valid_caps subject empty_caps"
  by (simp add: valid_caps_def empty_caps_def)

lemma suffix_drop_substring:
  "is_substring (drop n xs) (xs @ ys)"
  unfolding is_substring_def
  by (metis append_assoc append_take_drop_id)

lemma capture_update_valid_caps:
  assumes "valid_caps (l @ r) caps"
  shows "valid_caps (l @ r) (pcaps (capture_update n l0 (PState l r caps)))"
  using assms suffix_drop_substring[of "length l0" l r]
  by (auto simp add: capture_update_def valid_caps_def)

lemma first_nonempty_map_iff:
  "y \<in> set (first_nonempty_map f xs) \<longleftrightarrow>
    (\<exists>pre x post.
      xs = pre @ x # post \<and>
      y \<in> set (f x) \<and>
      (\<forall>z \<in> set pre. f z = []))"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "f a = []")
    case True
    have "y \<in> set (first_nonempty_map f (a # xs)) \<longleftrightarrow>
      y \<in> set (first_nonempty_map f xs)"
      using True by simp
    also have "... \<longleftrightarrow>
      (\<exists>pre x post.
        xs = pre @ x # post \<and>
        y \<in> set (f x) \<and>
        (\<forall>z \<in> set pre. f z = []))"
      using Cons by simp
    also have "... \<longleftrightarrow>
      (\<exists>pre x post.
        a # xs = pre @ x # post \<and>
        y \<in> set (f x) \<and>
        (\<forall>z \<in> set pre. f z = []))"
    proof
      assume "\<exists>pre x post.
        xs = pre @ x # post \<and>
        y \<in> set (f x) \<and>
        (\<forall>z \<in> set pre. f z = [])"
      then obtain pre x post where
        "xs = pre @ x # post" "y \<in> set (f x)" "\<forall>z \<in> set pre. f z = []"
        by blast
      then have
        "a # xs = (a # pre) @ x # post"
        "y \<in> set (f x)"
        "\<forall>z \<in> set (a # pre). f z = []"
        using True by auto
      then show "\<exists>pre x post.
        a # xs = pre @ x # post \<and>
        y \<in> set (f x) \<and>
        (\<forall>z \<in> set pre. f z = [])"
        by blast
    next
      assume "\<exists>pre x post.
        a # xs = pre @ x # post \<and>
        y \<in> set (f x) \<and>
        (\<forall>z \<in> set pre. f z = [])"
      then obtain pre x post where p:
        "a # xs = pre @ x # post" "y \<in> set (f x)" "\<forall>z \<in> set pre. f z = []"
        by blast
      show "\<exists>pre x post.
        xs = pre @ x # post \<and>
        y \<in> set (f x) \<and>
        (\<forall>z \<in> set pre. f z = [])"
      proof (cases pre)
        case Nil
        then have "x = a"
          using p by simp
        then show ?thesis
          using True p by simp
      next
        case (Cons b pre')
        then have "xs = pre' @ x # post"
          using p by simp
        moreover have "\<forall>z \<in> set pre'. f z = []"
          using p Cons by simp
        ultimately show ?thesis
          using p by blast
      qed
    qed
    finally show ?thesis .
  next
    case False
    show ?thesis
    proof
      assume "y \<in> set (first_nonempty_map f (a # xs))"
      then have "y \<in> set (f a)"
        using False by simp
      then show "\<exists>pre x post.
        a # xs = pre @ x # post \<and>
        y \<in> set (f x) \<and>
        (\<forall>z \<in> set pre. f z = [])"
        by (intro exI[of _ "[]"] exI[of _ a] exI[of _ xs]) simp
    next
      assume "\<exists>pre x post.
        a # xs = pre @ x # post \<and>
        y \<in> set (f x) \<and>
        (\<forall>z \<in> set pre. f z = [])"
      then obtain pre x post where p:
        "a # xs = pre @ x # post" "y \<in> set (f x)" "\<forall>z \<in> set pre. f z = []"
        by blast
      have "y \<in> set (f a)"
      proof (cases pre)
        case Nil
        then show ?thesis
          using p by simp
      next
        case (Cons b pre')
        then have "f a = []"
          using p by simp
        then show ?thesis
          using False by simp
      qed
      then show "y \<in> set (first_nonempty_map f (a # xs))"
        using False by simp
    qed
  qed
qed

lemma first_nonempty_map_empty_iff:
  "first_nonempty_map f xs = [] \<longleftrightarrow> (\<forall>x \<in> set xs. f x = [])"
  by (induct xs) (auto simp add: Let_def split: if_splits)

lemma pmatch_consumes_prefix:
  "st' \<in> set (pmatch fuel r st) \<Longrightarrow> consumes_prefix st st'"
and qmatch_consumes_prefix:
  "st' \<in> set (qmatch fuel q lo hi r st) \<Longrightarrow> consumes_prefix st st'"
proof -
  have both:
    "(\<forall>r st st'. st' \<in> set (pmatch fuel r st) \<longrightarrow> consumes_prefix st st') \<and>
     (\<forall>q lo hi r st st'.
        st' \<in> set (qmatch fuel q lo hi r st) \<longrightarrow> consumes_prefix st st')"
  proof (induct fuel)
    case 0
    then show ?case by simp
  next
    case (Suc fuel)
    then have pmIH:
      "\<And>r st st'. st' \<in> set (pmatch fuel r st) \<Longrightarrow> consumes_prefix st st'"
      and qmIH:
      "\<And>q lo hi r st st'.
        st' \<in> set (qmatch fuel q lo hi r st) \<Longrightarrow> consumes_prefix st st'"
      by auto
    show ?case
    proof (intro conjI)
      show "\<forall>r st st'. st' \<in> set (pmatch (Suc fuel) r st) \<longrightarrow>
        consumes_prefix st st'"
      proof (intro allI impI)
        fix r st st'
        assume h: "st' \<in> set (pmatch (Suc fuel) r st)"
        show "consumes_prefix st st'"
        proof (cases r)
          case PFail
          then show ?thesis using h by simp
        next
          case PEps
          then show ?thesis using h by simp
        next
          case (PChar c)
          then show ?thesis
          proof (cases st)
            case (PState l s caps)
            show ?thesis
            proof (cases s)
              case Nil
              then show ?thesis using h PChar PState by simp
            next
              case (Cons d rest)
              then have "st' = PState (l @ [d]) rest caps"
                using h PChar PState by auto
              then show ?thesis
                using PState Cons by (auto simp add: consumes_prefix_def)
            qed
          qed
        next
          case (PClass C)
          then show ?thesis
          proof (cases st)
            case (PState l s caps)
            show ?thesis
            proof (cases s)
              case Nil
              then show ?thesis using h PClass PState by simp
            next
              case (Cons d rest)
              then have "st' = PState (l @ [d]) rest caps"
                using h PClass PState by auto
              then show ?thesis
                using PState Cons by (auto simp add: consumes_prefix_def)
            qed
          qed
        next
          case (PDot excluded)
          then show ?thesis
          proof (cases st)
            case (PState l s caps)
            show ?thesis
            proof (cases s)
              case Nil
              then show ?thesis using h PDot PState by simp
            next
              case (Cons d rest)
              then have "st' = PState (l @ [d]) rest caps"
                using h PDot PState by auto
              then show ?thesis
                using PState Cons by (auto simp add: consumes_prefix_def)
            qed
          qed
        next
          case (PSeq r1 r2)
          then obtain mid where
            mid: "mid \<in> set (pmatch fuel r1 st)"
            and out: "st' \<in> set (pmatch fuel r2 mid)"
            using h by auto
          have "consumes_prefix st mid"
            using pmIH[OF mid] .
          moreover have "consumes_prefix mid st'"
            using pmIH[OF out] .
          ultimately show ?thesis
            using consumes_prefix_trans by blast
        next
          case (PAlt r1 r2)
          then show ?thesis
            using h pmIH by auto
        next
          case (PQuant q lo hi r)
          then show ?thesis
            using h qmIH by simp
        next
          case (PCapture n r)
          then obtain l s caps mid where
            st: "st = PState l s caps"
            and mid: "mid \<in> set (pmatch fuel r (PState l s caps))"
            and out: "st' = capture_update n l mid"
            using h by (cases st) auto
          have "consumes_prefix (PState l s caps) mid"
            using pmIH[OF mid] .
          then show ?thesis
            using st out by simp
        next
          case (PBackref n)
          then show ?thesis
          proof (cases st)
            case (PState l s caps)
            show ?thesis
            proof (cases "caps n")
              case None
              then show ?thesis
                using h PBackref PState by simp
            next
              case (Some w)
              then show ?thesis
                using h PBackref PState consumes_prefix_backref by auto
            qed
          qed
        next
          case (PAtomic r)
          then have "st' \<in> set (pmatch fuel r st)"
            using h first_only_subset by auto
          then show ?thesis
            using pmIH by blast
        next
          case (PLook positive r)
          then show ?thesis
            using h by (auto split: if_splits)
        next
          case (PLookBehind positive r)
          then show ?thesis
            using h by (cases st) (auto simp add: Let_def split: if_splits)
        next
          case (PCond n yes no)
          then show ?thesis
            using h pmIH by (cases "pcaps st n = None") auto
        next
          case (PWordBoundary W positive)
          then show ?thesis
            using h by (cases st) (auto split: if_splits)
        next
          case (PLineStart NL)
          then show ?thesis
            using h by (cases st) (auto split: if_splits)
        next
          case (PLineEnd NL)
          then show ?thesis
            using h by (cases st) (auto split: if_splits)
        next
          case PStart
          then show ?thesis
            using h by (cases st) (auto split: if_splits)
        next
          case PEnd
          then show ?thesis
            using h by (cases st) (auto split: if_splits)
        qed
      qed
      show "\<forall>q lo hi r st st'.
        st' \<in> set (qmatch (Suc fuel) q lo hi r st) \<longrightarrow>
        consumes_prefix st st'"
      proof (intro allI impI)
        fix q lo hi r st st'
        assume h: "st' \<in> set (qmatch (Suc fuel) q lo hi r st)"
        show "consumes_prefix st st'"
        proof (cases "0 < lo")
          case True
          show ?thesis
          proof (cases "can_take hi")
            case False
            then show ?thesis using h True by simp
          next
            case True
            from h \<open>0 < lo\<close> True obtain mid where
              mid: "mid \<in> set (progress_outputs st (pmatch fuel r st))"
              and out: "st' \<in> set (qmatch fuel q (lo - 1) (dec_bound hi) r mid)"
              by (auto simp add: progress_outputs_def)
            have "consumes_prefix st mid"
              using mid pmIH progress_outputs_subset by blast
            moreover have "consumes_prefix mid st'"
              using qmIH[OF out] .
            ultimately show ?thesis
              using consumes_prefix_trans by blast
          qed
        next
          case False
          then have lo0: "lo = 0" by simp
          show ?thesis
          proof (cases "can_take hi")
            case False
            then show ?thesis using h lo0 by simp
          next
            case True
            let ?next = "progress_outputs st (pmatch fuel r st)"
            show ?thesis
            proof (cases q)
              case Greedy
              then consider
                (stop) "st' = st" |
                (more) mid where
                  "mid \<in> set ?next"
                  "st' \<in> set (qmatch fuel Greedy 0 (dec_bound hi) r mid)"
                using h lo0 True by (auto simp add: Let_def)
              then show ?thesis
              proof cases
                case stop
                then show ?thesis by simp
              next
                case (more mid)
                have "consumes_prefix st mid"
                  using more(1) pmIH progress_outputs_subset by blast
                moreover have "consumes_prefix mid st'"
                  using qmIH[OF more(2)] .
                ultimately show ?thesis
                  using consumes_prefix_trans by blast
              qed
            next
              case Lazy
              then consider
                (stop) "st' = st" |
                (more) mid where
                  "mid \<in> set ?next"
                  "st' \<in> set (qmatch fuel Lazy 0 (dec_bound hi) r mid)"
                using h lo0 True by (auto simp add: Let_def)
              then show ?thesis
              proof cases
                case stop
                then show ?thesis by simp
              next
                case (more mid)
                have "consumes_prefix st mid"
                  using more(1) pmIH progress_outputs_subset by blast
                moreover have "consumes_prefix mid st'"
                  using qmIH[OF more(2)] .
                ultimately show ?thesis
                  using consumes_prefix_trans by blast
              qed
            next
              case Possessive
              show ?thesis
              proof (cases ?next)
                case Nil
                then show ?thesis
                  using h lo0 \<open>can_take hi\<close> Possessive by (simp add: Let_def)
              next
                case (Cons mid rest)
                then have mid: "mid \<in> set ?next"
                  by simp
                have out: "st' \<in> set (qmatch fuel Possessive 0 (dec_bound hi) r mid)"
                  using h lo0 \<open>can_take hi\<close> Possessive Cons by (simp add: Let_def)
                have "consumes_prefix st mid"
                  using mid pmIH progress_outputs_subset by blast
                moreover have "consumes_prefix mid st'"
                  using qmIH[OF out] .
                ultimately show ?thesis
                  using consumes_prefix_trans by blast
              qed
            next
              case Linear
              show ?thesis
              proof (cases ?next)
                case Nil
                then show ?thesis
                  using h lo0 \<open>can_take hi\<close> Linear by (simp add: Let_def)
              next
                case (Cons mid rest)
                then have mid: "mid \<in> set ?next"
                  by simp
                have out: "st' \<in> set (qmatch fuel Linear 0 (dec_bound hi) r mid)"
                  using h lo0 \<open>can_take hi\<close> Linear Cons by (simp add: Let_def)
                have "consumes_prefix st mid"
                  using mid pmIH progress_outputs_subset by blast
                moreover have "consumes_prefix mid st'"
                  using qmIH[OF out] .
                ultimately show ?thesis
                  using consumes_prefix_trans by blast
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  show "st' \<in> set (pmatch fuel r st) \<Longrightarrow> consumes_prefix st st'"
    using both by blast
  show "st' \<in> set (qmatch fuel q lo hi r st) \<Longrightarrow> consumes_prefix st st'"
    using both by blast
qed

lemma pmatch_preserves_spine:
  assumes "st' \<in> set (pmatch fuel r st)"
  shows "pleft st' @ pright st' = pleft st @ pright st"
proof -
  from pmatch_consumes_prefix[OF assms] obtain w where
    "pleft st' = pleft st @ w" "pright st = w @ pright st'"
    by (auto simp add: consumes_prefix_def)
  then show ?thesis
    by simp
qed

lemma pcre_fullmatch_sound:
  assumes "pcre_fullmatch fuel r s"
  shows "\<exists>caps. PState s [] caps \<in> set (pmatch fuel r (PState [] s empty_caps))"
proof -
  from assms obtain st' where
    st': "st' \<in> set (pmatch fuel r (PState [] s empty_caps))" "pright st' = []"
    by (auto simp add: pcre_fullmatch_def)
  from pmatch_consumes_prefix[OF st'(1)] obtain w where
    left: "pleft st' = w" and right: "s = w @ pright st'"
    by (auto simp add: consumes_prefix_def)
  then have "pleft st' = s"
    using st'(2) by simp
  then show ?thesis
    using st' by (cases st') auto
qed

lemma pmatch_valid_caps:
  "out \<in> set (pmatch fuel r st) \<Longrightarrow>
   valid_caps (pleft st @ pright st) (pcaps st) \<Longrightarrow>
   valid_caps (pleft st @ pright st) (pcaps out)"
and qmatch_valid_caps:
  "out \<in> set (qmatch fuel q lo hi r st) \<Longrightarrow>
   valid_caps (pleft st @ pright st) (pcaps st) \<Longrightarrow>
   valid_caps (pleft st @ pright st) (pcaps out)"
proof -
  have both:
    "(\<forall>r st out.
        out \<in> set (pmatch fuel r st) \<longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps st) \<longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps out)) \<and>
     (\<forall>q lo hi r st out.
        out \<in> set (qmatch fuel q lo hi r st) \<longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps st) \<longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps out))"
  proof (induct fuel)
    case 0
    then show ?case by simp
  next
    case (Suc fuel)
    then have pmIH:
      "\<And>r st out.
        out \<in> set (pmatch fuel r st) \<Longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps st) \<Longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps out)"
      and qmIH:
      "\<And>q lo hi r st out.
        out \<in> set (qmatch fuel q lo hi r st) \<Longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps st) \<Longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps out)"
      by auto
    show ?case
    proof (intro conjI)
      show "\<forall>r st out.
        out \<in> set (pmatch (Suc fuel) r st) \<longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps st) \<longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps out)"
      proof (intro allI impI)
        fix r st out
        assume h: "out \<in> set (pmatch (Suc fuel) r st)"
        assume valid: "valid_caps (pleft st @ pright st) (pcaps st)"
        show "valid_caps (pleft st @ pright st) (pcaps out)"
        proof (cases r)
          case PFail
          then show ?thesis using h by simp
        next
          case PEps
          then show ?thesis using h valid by simp
        next
          case (PChar c)
          then show ?thesis
            using h valid by (cases st; cases "pright st") (auto split: if_splits)
        next
          case (PClass C)
          then show ?thesis
            using h valid by (cases st; cases "pright st") (auto split: if_splits)
        next
          case (PDot excluded)
          then show ?thesis
            using h valid by (cases st; cases "pright st") (auto split: if_splits)
        next
          case (PSeq r1 r2)
          then obtain mid where
            mid: "mid \<in> set (pmatch fuel r1 st)"
            and out: "out \<in> set (pmatch fuel r2 mid)"
            using h by auto
          have mid_valid: "valid_caps (pleft st @ pright st) (pcaps mid)"
            using pmIH[OF mid valid] .
          have spine: "pleft mid @ pright mid = pleft st @ pright st"
            using pmatch_preserves_spine[OF mid] .
          have "valid_caps (pleft mid @ pright mid) (pcaps mid)"
            using mid_valid spine by simp
          then have "valid_caps (pleft mid @ pright mid) (pcaps out)"
            using pmIH[OF out] by blast
          then show ?thesis
            using spine by simp
        next
          case (PAlt r1 r2)
          then show ?thesis
            using h valid pmIH by auto
        next
          case (PQuant q lo hi r)
          then show ?thesis
            using h valid qmIH by simp
        next
          case (PCapture n r)
          then obtain l s caps mid where st: "st = PState l s caps"
            and mid: "mid \<in> set (pmatch fuel r (PState l s caps))"
            and out_eq: "out = capture_update n l mid"
            using h by (cases st) auto
          have mid_valid: "valid_caps (l @ s) (pcaps mid)"
            using pmIH[OF mid] valid st by simp
          have spine: "pleft mid @ pright mid = l @ s"
            using pmatch_preserves_spine[OF mid] by simp
          obtain lm rm capsm where mid_state: "mid = PState lm rm capsm"
            by (cases mid)
          have "valid_caps (lm @ rm) (pcaps mid)"
            using mid_valid spine mid_state by simp
          then have "valid_caps (lm @ rm) (pcaps (capture_update n l mid))"
            using capture_update_valid_caps[of lm rm capsm n l] mid_state by simp
          then show ?thesis
            using st out_eq spine mid_state by simp
        next
          case (PBackref n)
          then show ?thesis using h valid by (cases st) (auto split: option.splits if_splits)
        next
          case (PAtomic r)
          then have "out \<in> set (pmatch fuel r st)"
            using h first_only_subset by auto
          then show ?thesis
            using pmIH valid by blast
        next
          case (PLook x21 r)
          then show ?thesis using h valid by (auto split: if_splits)
        next
          case (PLookBehind x21 r)
          then show ?thesis using h valid by (cases st) (auto simp add: Let_def split: if_splits)
        next
          case (PCond n yes no)
          then show ?thesis
            using h valid pmIH by (cases "pcaps st n = None") auto
        next
          case (PWordBoundary W positive)
          then show ?thesis using h valid by (cases st) (auto split: if_splits)
        next
          case (PLineStart NL)
          then show ?thesis using h valid by (cases st) (auto split: if_splits)
        next
          case (PLineEnd NL)
          then show ?thesis using h valid by (cases st) (auto split: if_splits)
        next
          case PStart
          then show ?thesis using h valid by (cases st) (auto split: if_splits)
        next
          case PEnd
          then show ?thesis using h valid by (cases st) (auto split: if_splits)
        qed
      qed
      show "\<forall>q lo hi r st out.
        out \<in> set (qmatch (Suc fuel) q lo hi r st) \<longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps st) \<longrightarrow>
        valid_caps (pleft st @ pright st) (pcaps out)"
      proof (intro allI impI)
        fix q lo hi r st out
        assume h: "out \<in> set (qmatch (Suc fuel) q lo hi r st)"
        assume valid: "valid_caps (pleft st @ pright st) (pcaps st)"
        let ?subject = "pleft st @ pright st"
        show "valid_caps ?subject (pcaps out)"
        proof (cases "0 < lo")
          case True
          show ?thesis
          proof (cases "can_take hi")
            case False
            then show ?thesis using h True by simp
          next
            case True
            from h \<open>0 < lo\<close> True obtain mid where
              mid: "mid \<in> set (progress_outputs st (pmatch fuel r st))"
              and out: "out \<in> set (qmatch fuel q (lo - 1) (dec_bound hi) r mid)"
              by (auto simp add: progress_outputs_def)
            have mid_p: "mid \<in> set (pmatch fuel r st)"
              using mid progress_outputs_subset by blast
            have mid_valid: "valid_caps ?subject (pcaps mid)"
              using pmIH[OF mid_p valid] .
            have spine: "pleft mid @ pright mid = ?subject"
              using pmatch_preserves_spine[OF mid_p] .
            have "valid_caps (pleft mid @ pright mid) (pcaps mid)"
              using mid_valid spine by simp
            then have "valid_caps (pleft mid @ pright mid) (pcaps out)"
              using qmIH[OF out] by blast
            then show ?thesis
              using spine by simp
          qed
        next
          case False
          then have lo0: "lo = 0" by simp
          show ?thesis
          proof (cases "can_take hi")
            case False
            then show ?thesis using h lo0 valid by simp
          next
            case True
            let ?next = "progress_outputs st (pmatch fuel r st)"
            show ?thesis
            proof (cases q)
              case Greedy
              then consider
                (stop) "out = st" |
                (more) mid where
                  "mid \<in> set ?next"
                  "out \<in> set (qmatch fuel Greedy 0 (dec_bound hi) r mid)"
                using h lo0 True by (auto simp add: Let_def)
              then show ?thesis
              proof cases
                case stop
                then show ?thesis using valid by simp
              next
                case (more mid)
                have mid_p: "mid \<in> set (pmatch fuel r st)"
                  using more(1) progress_outputs_subset by blast
                have mid_valid: "valid_caps ?subject (pcaps mid)"
                  using pmIH[OF mid_p valid] .
                have spine: "pleft mid @ pright mid = ?subject"
                  using pmatch_preserves_spine[OF mid_p] .
                have "valid_caps (pleft mid @ pright mid) (pcaps mid)"
                  using mid_valid spine by simp
                then have "valid_caps (pleft mid @ pright mid) (pcaps out)"
                  using qmIH[OF more(2)] by blast
                then show ?thesis using spine by simp
              qed
            next
              case Lazy
              then consider
                (stop) "out = st" |
                (more) mid where
                  "mid \<in> set ?next"
                  "out \<in> set (qmatch fuel Lazy 0 (dec_bound hi) r mid)"
                using h lo0 True by (auto simp add: Let_def)
              then show ?thesis
              proof cases
                case stop
                then show ?thesis using valid by simp
              next
                case (more mid)
                have mid_p: "mid \<in> set (pmatch fuel r st)"
                  using more(1) progress_outputs_subset by blast
                have mid_valid: "valid_caps ?subject (pcaps mid)"
                  using pmIH[OF mid_p valid] .
                have spine: "pleft mid @ pright mid = ?subject"
                  using pmatch_preserves_spine[OF mid_p] .
                have "valid_caps (pleft mid @ pright mid) (pcaps mid)"
                  using mid_valid spine by simp
                then have "valid_caps (pleft mid @ pright mid) (pcaps out)"
                  using qmIH[OF more(2)] by blast
                then show ?thesis using spine by simp
              qed
            next
              case Possessive
              show ?thesis
              proof (cases ?next)
                case Nil
                then show ?thesis
                  using h lo0 \<open>can_take hi\<close> Possessive valid by (simp add: Let_def)
              next
                case (Cons mid rest)
                then have mid: "mid \<in> set ?next"
                  by simp
                have out: "out \<in> set (qmatch fuel Possessive 0 (dec_bound hi) r mid)"
                  using h lo0 \<open>can_take hi\<close> Possessive Cons by (simp add: Let_def)
                have mid_p: "mid \<in> set (pmatch fuel r st)"
                  using mid progress_outputs_subset by blast
                have mid_valid: "valid_caps ?subject (pcaps mid)"
                  using pmIH[OF mid_p valid] .
                have spine: "pleft mid @ pright mid = ?subject"
                  using pmatch_preserves_spine[OF mid_p] .
                have "valid_caps (pleft mid @ pright mid) (pcaps mid)"
                  using mid_valid spine by simp
                then have "valid_caps (pleft mid @ pright mid) (pcaps out)"
                  using qmIH[OF out] by blast
                then show ?thesis using spine by simp
              qed
            next
              case Linear
              show ?thesis
              proof (cases ?next)
                case Nil
                then show ?thesis
                  using h lo0 \<open>can_take hi\<close> Linear valid by (simp add: Let_def)
              next
                case (Cons mid rest)
                then have mid: "mid \<in> set ?next" by simp
                have out: "out \<in> set (qmatch fuel Linear 0 (dec_bound hi) r mid)"
                  using h lo0 \<open>can_take hi\<close> Linear Cons by (simp add: Let_def)
                have mid_p: "mid \<in> set (pmatch fuel r st)"
                  using mid progress_outputs_subset by blast
                have mid_valid: "valid_caps ?subject (pcaps mid)"
                  using pmIH[OF mid_p valid] .
                have spine: "pleft mid @ pright mid = ?subject"
                  using pmatch_preserves_spine[OF mid_p] .
                have "valid_caps (pleft mid @ pright mid) (pcaps mid)"
                  using mid_valid spine by simp
                then have "valid_caps (pleft mid @ pright mid) (pcaps out)"
                  using qmIH[OF out] by blast
                then show ?thesis using spine by simp
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  show "out \<in> set (pmatch fuel r st) \<Longrightarrow>
    valid_caps (pleft st @ pright st) (pcaps st) \<Longrightarrow>
    valid_caps (pleft st @ pright st) (pcaps out)"
    using both by blast
  show "out \<in> set (qmatch fuel q lo hi r st) \<Longrightarrow>
    valid_caps (pleft st @ pright st) (pcaps st) \<Longrightarrow>
    valid_caps (pleft st @ pright st) (pcaps out)"
    using both by blast
qed

lemma set_concat_map_cong:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> set (f x) = set (g x)"
  shows "set (concat (map f xs)) = set (concat (map g xs))"
  using assms by (induct xs) auto

lemma set_concat_map_subset:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> set (f x) \<subseteq> set (g x)"
  shows "set (concat (map f xs)) \<subseteq> set (concat (map g xs))"
  using assms by (induct xs) auto

lemma set_concat_map_mono:
  assumes "set xs \<subseteq> set ys"
  shows "set (concat (map f xs)) \<subseteq> set (concat (map f ys))"
  using assms by (induct xs) auto

lemma length_le_one_set_unique:
  assumes "length xs \<le> 1"
    and "x \<in> set xs"
    and "y \<in> set xs"
  shows "x = y"
  using assms by (cases xs) auto

lemma length_le_one_member_singleton:
  assumes "length xs \<le> 1"
    and "x \<in> set xs"
  shows "xs = [x]"
  using assms by (cases xs) auto

lemma qmatch_greedy_lazy_set:
  "set (qmatch fuel Greedy lo hi r st) = set (qmatch fuel Lazy lo hi r st)"
proof (induct fuel arbitrary: lo hi st)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "0 < lo")
    case True
    show ?thesis
    proof (cases "can_take hi")
      case False
      then show ?thesis using True by simp
    next
      case True
      have "set (concat
          (map (qmatch fuel Greedy (lo - 1) (dec_bound hi) r)
            (progress_outputs st (pmatch fuel r st)))) =
        set (concat
          (map (qmatch fuel Lazy (lo - 1) (dec_bound hi) r)
            (progress_outputs st (pmatch fuel r st))))"
        by (rule set_concat_map_cong) (simp add: Suc.hyps)
      then show ?thesis
        using \<open>0 < lo\<close> \<open>can_take hi\<close> by simp
    qed
  next
    case False
    then have lo0: "lo = 0" by simp
    show ?thesis
    proof (cases "can_take hi")
      case False
      then show ?thesis using lo0 by simp
    next
      case True
      let ?next = "progress_outputs st (pmatch fuel r st)"
      have "set (concat
          (map (qmatch fuel Greedy 0 (dec_bound hi) r) ?next)) =
        set (concat
          (map (qmatch fuel Lazy 0 (dec_bound hi) r) ?next))"
        by (rule set_concat_map_cong) (simp add: Suc.hyps)
      then show ?thesis
        using lo0 \<open>can_take hi\<close> by (simp add: Let_def)
    qed
  qed
qed

lemma qmatch_possessive_subset_greedy:
  "set (qmatch fuel Possessive lo hi r st) \<subseteq> set (qmatch fuel Greedy lo hi r st)"
proof (induct fuel arbitrary: lo hi st)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "0 < lo")
    case True
    show ?thesis
    proof (cases "can_take hi")
      case False
      then show ?thesis using True by simp
    next
      case True
      have "set (concat
          (map (qmatch fuel Possessive (lo - 1) (dec_bound hi) r)
            (progress_outputs st (pmatch fuel r st)))) \<subseteq>
        set (concat
          (map (qmatch fuel Greedy (lo - 1) (dec_bound hi) r)
            (progress_outputs st (pmatch fuel r st))))"
        by (rule set_concat_map_subset) (simp add: Suc.hyps)
      then show ?thesis
        using \<open>0 < lo\<close> \<open>can_take hi\<close> by simp
    qed
  next
    case False
    then have lo0: "lo = 0" by simp
    show ?thesis
    proof (cases "can_take hi")
      case False
      then show ?thesis using lo0 by simp
    next
      case True
      let ?next = "progress_outputs st (pmatch fuel r st)"
      show ?thesis
      proof (cases ?next)
        case Nil
        then show ?thesis
          using lo0 \<open>can_take hi\<close> by (simp add: Let_def)
      next
        case (Cons mid rest)
        have rec_subset:
          "set (qmatch fuel Possessive 0 (dec_bound hi) r mid) \<subseteq>
           set (qmatch fuel Greedy 0 (dec_bound hi) r mid)"
          by (simp add: Suc.hyps)
        have greedy_in_more:
          "set (qmatch fuel Greedy 0 (dec_bound hi) r mid) \<subseteq>
           set (concat (map (qmatch fuel Greedy 0 (dec_bound hi) r) ?next))"
          using Cons by auto
        show ?thesis
          using lo0 \<open>can_take hi\<close> Cons rec_subset greedy_in_more
          by (auto simp add: Let_def)
      qed
    qed
  qed
qed

lemma pmatch_possessive_quant_subset_greedy:
  "set (pmatch fuel (PQuant Possessive lo hi r) st) \<subseteq>
   set (pmatch fuel (PQuant Greedy lo hi r) st)"
proof (cases fuel)
  case 0
  then show ?thesis by simp
next
  case (Suc fuel')
  then show ?thesis
    using qmatch_possessive_subset_greedy[of fuel' lo hi r st] by simp
qed

lemma pmatch_seq_possessive_quant_subset_greedy:
  "set (pmatch fuel (PSeq (PQuant Possessive lo hi r) tail) st) \<subseteq>
   set (pmatch fuel (PSeq (PQuant Greedy lo hi r) tail) st)"
proof (cases fuel)
  case 0
  then show ?thesis by simp
next
  case (Suc fuel')
  have first_subset:
    "set (pmatch fuel' (PQuant Possessive lo hi r) st) \<subseteq>
     set (pmatch fuel' (PQuant Greedy lo hi r) st)"
    by (rule pmatch_possessive_quant_subset_greedy)
  have "set (concat
      (map (pmatch fuel' tail) (pmatch fuel' (PQuant Possessive lo hi r) st))) \<subseteq>
    set (concat
      (map (pmatch fuel' tail) (pmatch fuel' (PQuant Greedy lo hi r) st)))"
    by (rule set_concat_map_mono) (rule first_subset)
  then show ?thesis
    using Suc by simp
qed

lemma pcre_fullmatch_language_possessive_quant_subset_greedy:
  "pcre_fullmatch_language fuel (PQuant Possessive lo hi r) \<subseteq>
   pcre_fullmatch_language fuel (PQuant Greedy lo hi r)"
proof
  fix s
  assume "s \<in> pcre_fullmatch_language fuel (PQuant Possessive lo hi r)"
  then obtain out where out:
    "out \<in> set (pmatch fuel (PQuant Possessive lo hi r)
      (PState [] s empty_caps))"
    "pright out = []"
    by (auto simp add: pcre_fullmatch_language_def pcre_fullmatch_def)
  have "out \<in> set (pmatch fuel (PQuant Greedy lo hi r)
      (PState [] s empty_caps))"
    using out(1)
      pmatch_possessive_quant_subset_greedy[
        of fuel lo hi r "PState [] s empty_caps"]
    by (rule set_rev_mp)
  then have "pcre_fullmatch fuel (PQuant Greedy lo hi r) s"
    using out(2) by (auto simp add: pcre_fullmatch_def)
  then show "s \<in> pcre_fullmatch_language fuel (PQuant Greedy lo hi r)"
    by (simp add: pcre_fullmatch_language_def)
qed

lemma pcre_fullmatch_language_seq_possessive_quant_subset_greedy:
  "pcre_fullmatch_language fuel (PSeq (PQuant Possessive lo hi r) tail) \<subseteq>
   pcre_fullmatch_language fuel (PSeq (PQuant Greedy lo hi r) tail)"
proof
  fix s
  assume "s \<in> pcre_fullmatch_language fuel (PSeq (PQuant Possessive lo hi r) tail)"
  then obtain out where out:
    "out \<in> set (pmatch fuel (PSeq (PQuant Possessive lo hi r) tail)
      (PState [] s empty_caps))"
    "pright out = []"
    by (auto simp add: pcre_fullmatch_language_def pcre_fullmatch_def)
  have "out \<in> set (pmatch fuel (PSeq (PQuant Greedy lo hi r) tail)
      (PState [] s empty_caps))"
    using out(1)
      pmatch_seq_possessive_quant_subset_greedy[
        of fuel lo hi r tail "PState [] s empty_caps"]
    by (rule set_rev_mp)
  then have "pcre_fullmatch fuel (PSeq (PQuant Greedy lo hi r) tail) s"
    using out(2) by (auto simp add: pcre_fullmatch_def)
  then show "s \<in> pcre_fullmatch_language fuel (PSeq (PQuant Greedy lo hi r) tail)"
    by (simp add: pcre_fullmatch_language_def)
qed

lemma qmatch_linear_subset_possessive_zero:
  "set (qmatch fuel Linear 0 hi r st) \<subseteq> set (qmatch fuel Possessive 0 hi r st)"
proof (induct fuel arbitrary: lo hi st)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "can_take hi")
    case False
    then show ?thesis by simp
  next
    case True
    let ?next = "progress_outputs st (pmatch fuel r st)"
    show ?thesis
    proof (cases ?next)
      case Nil
      then show ?thesis
        using \<open>can_take hi\<close> by (simp add: Let_def)
    next
      case (Cons mid rest)
      have rec_subset:
        "set (qmatch fuel Linear 0 (dec_bound hi) r mid) \<subseteq>
         set (qmatch fuel Possessive 0 (dec_bound hi) r mid)"
        by (simp add: Suc.hyps)
      show ?thesis
        using \<open>can_take hi\<close> Cons rec_subset by (simp add: Let_def)
    qed
  qed
qed

lemma qmatch_possessive_zero_length_le_one:
  "length (qmatch fuel Possessive 0 hi r st) \<le> 1"
proof (induct fuel arbitrary: hi st)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "can_take hi")
    case False
    then show ?thesis by simp
  next
    case True
    let ?next = "progress_outputs st (pmatch fuel r st)"
    show ?thesis
    proof (cases ?next)
      case Nil
      then show ?thesis
        using True by (simp add: Let_def)
    next
      case (Cons mid rest)
      then show ?thesis
        using True Suc.hyps[of "dec_bound hi" mid] by (simp add: Let_def)
    qed
  qed
qed

lemma qmatch_possessive_zero_first_greedy:
  assumes "qmatch fuel Possessive 0 hi r st = [out]"
  shows "qmatch fuel Greedy 0 hi r st \<noteq> [] \<and>
    hd (qmatch fuel Greedy 0 hi r st) = out"
  using assms
proof (induct fuel arbitrary: hi st out)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "can_take hi")
    case False
    then show ?thesis using Suc.prems by simp
  next
    case True
    let ?next = "progress_outputs st (pmatch fuel r st)"
    show ?thesis
    proof (cases ?next)
      case Nil
      then show ?thesis
        using True Suc.prems by (simp add: Let_def)
    next
      case (Cons mid rest)
      then have rec_poss:
        "qmatch fuel Possessive 0 (dec_bound hi) r mid = [out]"
        using True Suc.prems by (simp add: Let_def)
      then have rec_greedy:
        "qmatch fuel Greedy 0 (dec_bound hi) r mid \<noteq> []"
        "hd (qmatch fuel Greedy 0 (dec_bound hi) r mid) = out"
        using Suc.hyps by blast+
      have greedy_unfold:
        "qmatch (Suc fuel) Greedy 0 hi r st =
          qmatch fuel Greedy 0 (dec_bound hi) r mid @
          concat (map (qmatch fuel Greedy 0 (dec_bound hi) r) rest) @ [st]"
        using True Cons by (simp add: Let_def)
      then show ?thesis
        using rec_greedy by simp
    qed
  qed
qed

lemma qmatch_lazy_zero_order:
  assumes "can_take hi"
  shows "qmatch (Suc fuel) Lazy 0 hi r st =
    st # concat (map (qmatch fuel Lazy 0 (dec_bound hi) r)
      (progress_outputs st (pmatch fuel r st)))"
  using assms by (simp add: Let_def)

lemma qmatch_greedy_zero_order:
  assumes "can_take hi"
  shows "qmatch (Suc fuel) Greedy 0 hi r st =
    concat (map (qmatch fuel Greedy 0 (dec_bound hi) r)
      (progress_outputs st (pmatch fuel r st))) @ [st]"
  using assms by (simp add: Let_def)

lemma qmatch_lazy_zero_first:
  assumes "can_take hi"
  shows "qmatch (Suc fuel) Lazy 0 hi r st \<noteq> [] \<and>
    hd (qmatch (Suc fuel) Lazy 0 hi r st) = st"
  using assms by (simp add: qmatch_lazy_zero_order)

lemma qmatch_greedy_zero_last:
  assumes "can_take hi"
  shows "qmatch (Suc fuel) Greedy 0 hi r st \<noteq> [] \<and>
    last (qmatch (Suc fuel) Greedy 0 hi r st) = st"
  using assms by (simp add: qmatch_greedy_zero_order)

lemma atomic_group_commits_to_first_result:
  "pmatch (Suc fuel) (PAtomic r) st = first_only (pmatch fuel r st)"
  by simp

lemma lookahead_is_zero_width:
  assumes "st' \<in> set (pmatch (Suc fuel) (PLook positive r) st)"
  shows "st' = st"
  using assms by (auto split: if_splits)

lemma lookbehind_is_zero_width:
  assumes "st' \<in> set (pmatch (Suc fuel) (PLookBehind positive r) (PState l s caps))"
  shows "st' = PState l s caps"
  using assms by (auto simp add: Let_def split: if_splits)

lemma word_boundary_is_zero_width:
  assumes "st' \<in> set (pmatch (Suc fuel) (PWordBoundary W positive) (PState l s caps))"
  shows "st' = PState l s caps"
  using assms by (auto split: if_splits)

lemma line_start_is_zero_width:
  assumes "st' \<in> set (pmatch (Suc fuel) (PLineStart NL) (PState l s caps))"
  shows "st' = PState l s caps"
  using assms by (auto split: if_splits)

lemma line_end_is_zero_width:
  assumes "st' \<in> set (pmatch (Suc fuel) (PLineEnd NL) (PState l s caps))"
  shows "st' = PState l s caps"
  using assms by (auto split: if_splits)

lemma dot_consumes_one:
  assumes "d \<notin> excluded"
  shows "pmatch (Suc fuel) (PDot excluded) (PState l (d # s) caps) =
    [PState (l @ [d]) s caps]"
  using assms by simp

lemma backref_consumes_stored_text:
  assumes "starts_with w s"
  shows
    "pmatch (Suc fuel) (PBackref n) (PState l s (caps(n := Some w))) =
      [PState (l @ w) (drop (length w) s) (caps(n := Some w))]"
  using assms by simp

section \<open>Relational Trace Semantics\<close>

definition ptrace :: "nat \<Rightarrow> pcre \<Rightarrow> pstate \<Rightarrow> pstate \<Rightarrow> bool"
where
  "ptrace fuel r st out \<longleftrightarrow> out \<in> set (pmatch fuel r st)"

definition qtrace ::
  "nat \<Rightarrow> qkind \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> pcre \<Rightarrow> pstate \<Rightarrow> pstate \<Rightarrow> bool"
where
  "qtrace fuel q lo hi r st out \<longleftrightarrow> out \<in> set (qmatch fuel q lo hi r st)"

definition leftmost_trace :: "nat \<Rightarrow> pcre \<Rightarrow> string \<Rightarrow> pstate \<Rightarrow> bool"
where
  "leftmost_trace fuel r s out \<longleftrightarrow>
    (\<exists>pre i post.
      [0..<Suc (length s)] = pre @ i # post \<and>
      ptrace fuel r (PState (take i s) (drop i s) empty_caps) out \<and>
      (\<forall>j \<in> set pre.
        \<not> (\<exists>out'. ptrace fuel r (PState (take j s) (drop j s) empty_caps) out')))"

theorem ptrace_iff_pmatch:
  "ptrace fuel r st out \<longleftrightarrow> out \<in> set (pmatch fuel r st)"
  by (simp add: ptrace_def)

theorem qtrace_iff_qmatch:
  "qtrace fuel q lo hi r st out \<longleftrightarrow> out \<in> set (qmatch fuel q lo hi r st)"
  by (simp add: qtrace_def)

theorem pcre_search_states_iff_leftmost_trace:
  "out \<in> set (pcre_search_states fuel r s) \<longleftrightarrow> leftmost_trace fuel r s out"
  by (simp add: pcre_search_states_def leftmost_trace_def
      ptrace_def first_nonempty_map_iff)

lemma pcre_search_iff_leftmost_trace:
  "pcre_search fuel r s \<longleftrightarrow> (\<exists>out. leftmost_trace fuel r s out)"
proof
  assume "pcre_search fuel r s"
  then have "pcre_search_states fuel r s \<noteq> []"
    by (simp add: pcre_search_def)
  then obtain out where "out \<in> set (pcre_search_states fuel r s)"
    by (cases "pcre_search_states fuel r s") auto
  then show "\<exists>out. leftmost_trace fuel r s out"
    using pcre_search_states_iff_leftmost_trace by blast
next
  assume "\<exists>out. leftmost_trace fuel r s out"
  then obtain out where "leftmost_trace fuel r s out"
    by blast
  then have "out \<in> set (pcre_search_states fuel r s)"
    using pcre_search_states_iff_leftmost_trace by blast
  then show "pcre_search fuel r s"
    by (auto simp add: pcre_search_def)
qed

lemma leftmost_trace_has_start:
  assumes "leftmost_trace fuel r s out"
  shows "\<exists>i \<le> length s. ptrace fuel r (PState (take i s) (drop i s) empty_caps) out"
proof -
  from assms obtain pre i post where i:
    "[0..<Suc (length s)] = pre @ i # post"
    "ptrace fuel r (PState (take i s) (drop i s) empty_caps) out"
    by (auto simp add: leftmost_trace_def)
  then have "i \<in> set [0..<Suc (length s)]"
    by auto
  then have "i = length s \<or> i < length s"
    by simp
  then have "i \<le> length s"
    by auto
  then show ?thesis
    using i by blast
qed

lemma pcre_search_state_preserves_subject:
  assumes "out \<in> set (pcre_search_states fuel r s)"
  shows "pleft out @ pright out = s"
proof -
  from assms have "leftmost_trace fuel r s out"
    by (simp add: pcre_search_states_iff_leftmost_trace)
  then obtain i where i:
    "i \<le> length s"
    "ptrace fuel r (PState (take i s) (drop i s) empty_caps) out"
    using leftmost_trace_has_start by blast
  then have "out \<in> set (pmatch fuel r (PState (take i s) (drop i s) empty_caps))"
    by (simp add: ptrace_def)
  from pmatch_preserves_spine[OF this] show ?thesis
    by simp
qed

lemma pcre_search_entries_iff:
  "(i, out) \<in> set (pcre_search_entries fuel r s) \<longleftrightarrow>
    (\<exists>pre post.
      [0..<Suc (length s)] = pre @ i # post \<and>
      ptrace fuel r (PState (take i s) (drop i s) empty_caps) out \<and>
      (\<forall>j \<in> set pre.
        \<not> (\<exists>out'. ptrace fuel r (PState (take j s) (drop j s) empty_caps) out')))"
  by (auto simp add: pcre_search_entries_def ptrace_def first_nonempty_map_iff)

lemma pcre_search_entries_start_bound:
  assumes "(i, out) \<in> set (pcre_search_entries fuel r s)"
  shows "i \<le> length s"
proof -
  from assms obtain pre post where
    "[0..<Suc (length s)] = pre @ i # post"
    by (auto simp add: pcre_search_entries_iff)
  then have "i \<in> set [0..<Suc (length s)]"
    by auto
  then have "i = length s \<or> i < length s"
    by simp
  then show ?thesis
    by auto
qed

lemma pcre_search_entries_preserves_subject:
  assumes "(i, out) \<in> set (pcre_search_entries fuel r s)"
  shows "pleft out @ pright out = s"
proof -
  from assms have "ptrace fuel r (PState (take i s) (drop i s) empty_caps) out"
    by (auto simp add: pcre_search_entries_iff)
  then have "out \<in> set (pmatch fuel r (PState (take i s) (drop i s) empty_caps))"
    by (simp add: ptrace_def)
  from pmatch_preserves_spine[OF this] show ?thesis
    by simp
qed

lemma pcre_search_entries_empty_iff:
  "pcre_search_entries fuel r s = [] \<longleftrightarrow> pcre_search_states fuel r s = []"
  by (simp add: pcre_search_entries_def pcre_search_states_def
      first_nonempty_map_empty_iff)

lemma pcre_exec_None_iff:
  "pcre_exec fuel r s = None \<longleftrightarrow> \<not> pcre_search fuel r s"
proof (cases "pcre_search_entries fuel r s")
  case Nil
  then have exec: "pcre_exec fuel r s = None"
    by (simp add: pcre_exec_def)
  from Nil have "\<not> pcre_search fuel r s"
    by (simp add: pcre_search_def pcre_search_entries_empty_iff)
  then show ?thesis
    using exec by simp
next
  case (Cons entry rest)
  then have "pcre_search_states fuel r s \<noteq> []"
    using pcre_search_entries_empty_iff[of fuel r s] by auto
  moreover from Cons have "pcre_exec fuel r s \<noteq> None"
    by (simp add: pcre_exec_def)
  then show ?thesis
    using calculation by (simp add: pcre_search_def)
qed

lemma pcre_exec_Some_iff:
  "pcre_exec fuel r s = Some res \<longleftrightarrow>
    (\<exists>entry rest.
      pcre_search_entries fuel r s = entry # rest \<and>
      res = result_of_entry entry)"
  by (cases "pcre_search_entries fuel r s")
     (auto simp add: pcre_exec_def)

lemma pcre_exec_success_iff_search:
  "(\<exists>res. pcre_exec fuel r s = Some res) \<longleftrightarrow> pcre_search fuel r s"
proof -
  have "(\<exists>res. pcre_exec fuel r s = Some res) \<longleftrightarrow> pcre_exec fuel r s \<noteq> None"
    by (cases "pcre_exec fuel r s") auto
  then show ?thesis
    by (simp add: pcre_exec_None_iff)
qed

lemma pcre_exec_first_entry:
  assumes "pcre_search_entries fuel r s = entry # rest"
  shows "pcre_exec fuel r s = Some (result_of_entry entry)"
  using assms by (simp add: pcre_exec_def)

lemma pcre_exec_sound:
  assumes "pcre_exec fuel r s = Some (PResult i j caps)"
  shows
    "i \<le> j \<and> j \<le> length s \<and>
     (\<exists>out.
        (i, out) \<in> set (pcre_search_entries fuel r s) \<and>
        ptrace fuel r (PState (take i s) (drop i s) empty_caps) out \<and>
        out = PState (take j s) (drop j s) caps)"
proof -
  obtain entry rest where entries:
    "pcre_search_entries fuel r s = entry # rest"
    and result: "result_of_entry entry = PResult i j caps"
    using assms
    by (cases "pcre_search_entries fuel r s")
       (auto simp add: pcre_exec_def)
  obtain i0 st where entry: "entry = (i0, st)"
    by (cases entry)
  obtain l rs caps0 where st: "st = PState l rs caps0"
    by (cases st)
  from result entry st have vals:
    "i = i0" "j = length l" "caps = caps0"
    by (simp_all add: result_of_entry_def)
  have mem: "(i0, PState l rs caps0) \<in> set (pcre_search_entries fuel r s)"
    using entries entry st by simp
  then have start_bound: "i0 \<le> length s"
    using pcre_search_entries_start_bound by blast
  from mem have tr:
    "ptrace fuel r (PState (take i0 s) (drop i0 s) empty_caps) (PState l rs caps0)"
    by (auto simp add: pcre_search_entries_iff)
  then have pm:
    "PState l rs caps0 \<in> set (pmatch fuel r (PState (take i0 s) (drop i0 s) empty_caps))"
    by (simp add: ptrace_def)
  have subj: "l @ rs = s"
    using pcre_search_entries_preserves_subject[OF mem] by simp
  have end_bound: "length l \<le> length s"
    using arg_cong[OF subj, of length] by simp
  have start_before_end: "i0 \<le> length l"
  proof -
    from pmatch_consumes_prefix[OF pm] obtain w where
      "l = take i0 s @ w"
      by (auto simp add: consumes_prefix_def)
    then show ?thesis
      using start_bound by simp
  qed
  have out_shape:
    "PState l rs caps0 = PState (take (length l) s) (drop (length l) s) caps0"
    by (simp add: subj[symmetric])
  show ?thesis
    using vals mem tr end_bound start_before_end out_shape by auto
qed

lemma pcre_exec_valid_caps:
  assumes "pcre_exec fuel r s = Some (PResult i j caps)"
  shows "valid_caps s caps"
proof -
  from pcre_exec_sound[OF assms] obtain out where
    tr: "ptrace fuel r (PState (take i s) (drop i s) empty_caps) out"
    and out_eq: "out = PState (take j s) (drop j s) caps"
    by blast
  from tr have pm:
    "out \<in> set (pmatch fuel r (PState (take i s) (drop i s) empty_caps))"
    by (simp add: ptrace_def)
  have valid0: "valid_caps (take i s @ drop i s) empty_caps"
    by simp
  have cap_out: "valid_caps
      (pleft (PState (take i s) (drop i s) empty_caps) @
       pright (PState (take i s) (drop i s) empty_caps))
      (pcaps out)"
  proof (rule pmatch_valid_caps[
      where fuel = fuel and r = r and
        st = "PState (take i s) (drop i s) empty_caps" and out = out])
    show "out \<in> set (pmatch fuel r (PState (take i s) (drop i s) empty_caps))"
      using pm .
    show "valid_caps
        (pleft (PState (take i s) (drop i s) empty_caps) @
         pright (PState (take i s) (drop i s) empty_caps))
        (pcaps (PState (take i s) (drop i s) empty_caps))"
      using valid0 by simp
  qed
  then show ?thesis
    using out_eq by simp
qed

lemma ptrace_seq_iff:
  "ptrace (Suc fuel) (PSeq r1 r2) st out \<longleftrightarrow>
    (\<exists>mid. ptrace fuel r1 st mid \<and> ptrace fuel r2 mid out)"
  by (auto simp add: ptrace_def)

lemma ptrace_alt_iff:
  "ptrace (Suc fuel) (PAlt r1 r2) st out \<longleftrightarrow>
    ptrace fuel r1 st out \<or> ptrace fuel r2 st out"
  by (auto simp add: ptrace_def)

lemma ptrace_dot_iff:
  "ptrace (Suc fuel) (PDot excluded) (PState l s caps) out \<longleftrightarrow>
    (\<exists>d rest. s = d # rest \<and> d \<notin> excluded \<and>
      out = PState (l @ [d]) rest caps)"
  by (cases s) (auto simp add: ptrace_def)

lemma ptrace_quant_iff:
  "ptrace (Suc fuel) (PQuant q lo hi r) st out \<longleftrightarrow>
    qtrace fuel q lo hi r st out"
  by (simp add: ptrace_def qtrace_def)

lemma ptrace_capture_iff:
  "ptrace (Suc fuel) (PCapture n r) (PState l s caps) out \<longleftrightarrow>
    (\<exists>out0. ptrace fuel r (PState l s caps) out0 \<and>
      out = capture_update n l out0)"
  by (auto simp add: ptrace_def)

lemma ptrace_backref_iff:
  "ptrace (Suc fuel) (PBackref n) (PState l s caps) out \<longleftrightarrow>
    (\<exists>w. caps n = Some w \<and> starts_with w s \<and>
      out = PState (l @ w) (drop (length w) s) caps)"
  by (auto simp add: ptrace_def split: option.splits if_splits)

lemma ptrace_atomic_iff:
  "ptrace (Suc fuel) (PAtomic r) st out \<longleftrightarrow>
    out \<in> set (first_only (pmatch fuel r st))"
  by (simp add: ptrace_def)

lemma ptrace_atomic_first_result:
  assumes "ptrace (Suc fuel) (PAtomic r) st out"
  shows "\<exists>rest. pmatch fuel r st = out # rest"
proof -
  have out: "out \<in> set (first_only (pmatch fuel r st))"
    using assms by (simp add: ptrace_atomic_iff)
  show ?thesis
  proof (cases "pmatch fuel r st")
    case Nil
    then show ?thesis using out by simp
  next
    case (Cons x rest)
    then have "out = x" using out by simp
    then have "pmatch fuel r st = out # rest" using Cons by simp
    then show ?thesis ..
  qed
qed

lemma ptrace_atomic_unique:
  assumes "ptrace (Suc fuel) (PAtomic r) st out1"
    and "ptrace (Suc fuel) (PAtomic r) st out2"
  shows "out1 = out2"
proof -
  have len: "length (first_only (pmatch fuel r st)) \<le> 1"
    using first_only_length_le_one .
  have out1: "out1 \<in> set (first_only (pmatch fuel r st))"
    using assms(1) by (simp add: ptrace_atomic_iff)
  have out2: "out2 \<in> set (first_only (pmatch fuel r st))"
    using assms(2) by (simp add: ptrace_atomic_iff)
  show ?thesis
    using length_le_one_set_unique[OF len out1 out2] .
qed

lemma ptrace_look_iff:
  "ptrace (Suc fuel) (PLook positive r) st out \<longleftrightarrow>
    out = st \<and>
    ((positive \<and> (\<exists>out0. ptrace fuel r st out0)) \<or>
     (\<not> positive \<and> \<not> (\<exists>out0. ptrace fuel r st out0)))"
  by (cases "pmatch fuel r st") (auto simp add: ptrace_def split: if_splits)

lemma ptrace_lookbehind_iff:
  "ptrace (Suc fuel) (PLookBehind positive r) (PState l s caps) out \<longleftrightarrow>
    out = PState l s caps \<and>
    ((positive \<and>
      (\<exists>pre suf out0.
        (pre, suf) \<in> set (splits l) \<and>
        ptrace fuel r (PState pre suf caps) out0 \<and>
        pleft out0 = l \<and> pright out0 = [])) \<or>
     (\<not> positive \<and>
      \<not> (\<exists>pre suf out0.
        (pre, suf) \<in> set (splits l) \<and>
        ptrace fuel r (PState pre suf caps) out0 \<and>
        pleft out0 = l \<and> pright out0 = [])))"
  by (auto simp add: ptrace_def Let_def split: if_splits)

lemma ptrace_cond_iff:
  "ptrace (Suc fuel) (PCond n yes no) st out \<longleftrightarrow>
    (if pcaps st n = None then ptrace fuel no st out else ptrace fuel yes st out)"
  by (simp add: ptrace_def)

lemma ptrace_word_boundary_iff:
  "ptrace (Suc fuel) (PWordBoundary W positive) (PState l s caps) out \<longleftrightarrow>
    out = PState l s caps \<and> word_boundary W l s = positive"
  by (auto simp add: ptrace_def split: if_splits)

lemma ptrace_word_boundary_zero_width:
  assumes "ptrace (Suc fuel) (PWordBoundary W positive) (PState l s caps) out"
  shows "out = PState l s caps"
  using assms by (auto simp add: ptrace_word_boundary_iff)

lemma ptrace_line_start_iff:
  "ptrace (Suc fuel) (PLineStart NL) (PState l s caps) out \<longleftrightarrow>
    out = PState l s caps \<and> line_start NL l"
  by (auto simp add: ptrace_def split: if_splits)

lemma ptrace_line_end_iff:
  "ptrace (Suc fuel) (PLineEnd NL) (PState l s caps) out \<longleftrightarrow>
    out = PState l s caps \<and> line_end NL s"
  by (auto simp add: ptrace_def split: if_splits)

lemma ptrace_line_start_zero_width:
  assumes "ptrace (Suc fuel) (PLineStart NL) (PState l s caps) out"
  shows "out = PState l s caps"
  using assms by (auto simp add: ptrace_line_start_iff)

lemma ptrace_line_end_zero_width:
  assumes "ptrace (Suc fuel) (PLineEnd NL) (PState l s caps) out"
  shows "out = PState l s caps"
  using assms by (auto simp add: ptrace_line_end_iff)

lemma qtrace_must_iff:
  assumes "0 < lo" "can_take hi"
  shows "qtrace (Suc fuel) q lo hi r st out \<longleftrightarrow>
    (\<exists>mid. mid \<in> set (progress_outputs st (pmatch fuel r st)) \<and>
      qtrace fuel q (lo - 1) (dec_bound hi) r mid out)"
  using assms by (auto simp add: qtrace_def)

lemma qtrace_stop_bound_iff:
  assumes "lo = 0" "\<not> can_take hi"
  shows "qtrace (Suc fuel) q lo hi r st out \<longleftrightarrow> out = st"
  using assms by (auto simp add: qtrace_def)

lemma qtrace_greedy_zero_iff:
  assumes "can_take hi"
  shows "qtrace (Suc fuel) Greedy 0 hi r st out \<longleftrightarrow>
    out = st \<or>
    (\<exists>mid. mid \<in> set (progress_outputs st (pmatch fuel r st)) \<and>
      qtrace fuel Greedy 0 (dec_bound hi) r mid out)"
  using assms by (auto simp add: qtrace_def Let_def)

lemma qtrace_lazy_zero_iff:
  assumes "can_take hi"
  shows "qtrace (Suc fuel) Lazy 0 hi r st out \<longleftrightarrow>
    out = st \<or>
    (\<exists>mid. mid \<in> set (progress_outputs st (pmatch fuel r st)) \<and>
      qtrace fuel Lazy 0 (dec_bound hi) r mid out)"
  using assms by (auto simp add: qtrace_def Let_def)

lemma qtrace_possessive_zero_iff:
  assumes "can_take hi"
  shows "qtrace (Suc fuel) Possessive 0 hi r st out \<longleftrightarrow>
    (case progress_outputs st (pmatch fuel r st) of
      [] \<Rightarrow> out = st
    | mid # rest \<Rightarrow> qtrace fuel Possessive 0 (dec_bound hi) r mid out)"
  using assms by (auto simp add: qtrace_def Let_def split: list.splits)

lemma qtrace_possessive_zero_unique:
  assumes "qtrace fuel Possessive 0 hi r st out1"
    and "qtrace fuel Possessive 0 hi r st out2"
  shows "out1 = out2"
  using assms
    qmatch_possessive_zero_length_le_one[of fuel hi r st]
    length_le_one_set_unique[of "qmatch fuel Possessive 0 hi r st" out1 out2]
  by (simp add: qtrace_def)

lemma qtrace_possessive_zero_first_greedy:
  assumes "qtrace fuel Possessive 0 hi r st out"
  shows "qmatch fuel Greedy 0 hi r st \<noteq> [] \<and>
    hd (qmatch fuel Greedy 0 hi r st) = out"
proof -
  have poss_len: "length (qmatch fuel Possessive 0 hi r st) \<le> 1"
    using qmatch_possessive_zero_length_le_one .
  have poss_mem: "out \<in> set (qmatch fuel Possessive 0 hi r st)"
    using assms by (simp add: qtrace_def)
  have poss_eq: "qmatch fuel Possessive 0 hi r st = [out]"
    using length_le_one_member_singleton[OF poss_len poss_mem] .
  then show ?thesis
    by (rule qmatch_possessive_zero_first_greedy)
qed

lemma qtrace_linear_zero_iff:
  assumes "can_take hi"
  shows "qtrace (Suc fuel) Linear 0 hi r st out \<longleftrightarrow>
    (case progress_outputs st (pmatch fuel r st) of
      [] \<Rightarrow> out = st
    | mid # rest \<Rightarrow> qtrace fuel Linear 0 (dec_bound hi) r mid out)"
  using assms by (auto simp add: qtrace_def Let_def split: list.splits)

section \<open>Finite Subpattern Call Programs\<close>

datatype ppcre =
  PAtom pcre
| PCall nat
| PProgSeq ppcre ppcre
| PProgAlt ppcre ppcre
| PProgAtomic ppcre
| PProgQuant qkind nat "nat option" ppcre

type_synonym penv = "nat \<Rightarrow> ppcre option"

fun pmatch_prog :: "nat \<Rightarrow> penv \<Rightarrow> ppcre \<Rightarrow> pstate \<Rightarrow> pstate list"
and qmatch_prog :: "nat \<Rightarrow> penv \<Rightarrow> qkind \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> ppcre \<Rightarrow> pstate \<Rightarrow> pstate list"
where
  "pmatch_prog 0 env r st = []"
| "pmatch_prog (Suc fuel) env (PAtom r) st = pmatch fuel r st"
| "pmatch_prog (Suc fuel) env (PCall n) st =
    (case env n of None \<Rightarrow> [] | Some r \<Rightarrow> pmatch_prog fuel env r st)"
| "pmatch_prog (Suc fuel) env (PProgSeq r1 r2) st =
    concat (map (pmatch_prog fuel env r2) (pmatch_prog fuel env r1 st))"
| "pmatch_prog (Suc fuel) env (PProgAlt r1 r2) st =
    pmatch_prog fuel env r1 st @ pmatch_prog fuel env r2 st"
| "pmatch_prog (Suc fuel) env (PProgAtomic r) st =
    first_only (pmatch_prog fuel env r st)"
| "pmatch_prog (Suc fuel) env (PProgQuant q lo hi r) st =
    qmatch_prog fuel env q lo hi r st"
| "qmatch_prog 0 env q lo hi r st = []"
| "qmatch_prog (Suc fuel) env q lo hi r st =
    (if 0 < lo then
       (if can_take hi
        then concat
          (map (qmatch_prog fuel env q (lo - 1) (dec_bound hi) r)
            (progress_outputs st (pmatch_prog fuel env r st)))
        else [])
     else if can_take hi then
       (let next = progress_outputs st (pmatch_prog fuel env r st);
            more = concat (map (qmatch_prog fuel env q 0 (dec_bound hi) r) next)
        in case q of
          Greedy \<Rightarrow> more @ [st]
        | Lazy \<Rightarrow> st # more
        | Possessive \<Rightarrow>
            (case next of
              [] \<Rightarrow> [st]
            | st1 # rest \<Rightarrow> qmatch_prog fuel env Possessive 0 (dec_bound hi) r st1)
        | Linear \<Rightarrow>
            (case next of
              [] \<Rightarrow> [st]
            | st1 # rest \<Rightarrow> qmatch_prog fuel env Linear 0 (dec_bound hi) r st1))
     else [st])"

definition pprog_trace :: "nat \<Rightarrow> penv \<Rightarrow> ppcre \<Rightarrow> pstate \<Rightarrow> pstate \<Rightarrow> bool"
where
  "pprog_trace fuel env r st out \<longleftrightarrow> out \<in> set (pmatch_prog fuel env r st)"

definition qprog_trace ::
  "nat \<Rightarrow> penv \<Rightarrow> qkind \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> ppcre \<Rightarrow> pstate \<Rightarrow> pstate \<Rightarrow> bool"
where
  "qprog_trace fuel env q lo hi r st out \<longleftrightarrow>
    out \<in> set (qmatch_prog fuel env q lo hi r st)"

lemma pmatch_prog_call_iff:
  "pprog_trace (Suc fuel) env (PCall n) st out \<longleftrightarrow>
    (case env n of None \<Rightarrow> False | Some r \<Rightarrow> pprog_trace fuel env r st out)"
  by (auto simp add: pprog_trace_def split: option.splits)

lemma pmatch_prog_atom_iff:
  "pprog_trace (Suc fuel) env (PAtom r) st out \<longleftrightarrow> ptrace fuel r st out"
  by (simp add: pprog_trace_def ptrace_def)

lemma pmatch_prog_consumes_prefix:
  "out \<in> set (pmatch_prog fuel env r st) \<Longrightarrow> consumes_prefix st out"
and qmatch_prog_consumes_prefix:
  "out \<in> set (qmatch_prog fuel env q lo hi r st) \<Longrightarrow> consumes_prefix st out"
proof -
  have both:
    "(\<forall>env r st out.
        out \<in> set (pmatch_prog fuel env r st) \<longrightarrow> consumes_prefix st out) \<and>
     (\<forall>env q lo hi r st out.
        out \<in> set (qmatch_prog fuel env q lo hi r st) \<longrightarrow> consumes_prefix st out)"
  proof (induct fuel)
    case 0
    then show ?case by simp
  next
    case (Suc fuel)
    then have pmIH:
      "\<And>env r st out.
        out \<in> set (pmatch_prog fuel env r st) \<Longrightarrow> consumes_prefix st out"
      and qmIH:
      "\<And>env q lo hi r st out.
        out \<in> set (qmatch_prog fuel env q lo hi r st) \<Longrightarrow> consumes_prefix st out"
      by auto
    show ?case
    proof (intro conjI)
      show "\<forall>env r st out.
        out \<in> set (pmatch_prog (Suc fuel) env r st) \<longrightarrow> consumes_prefix st out"
      proof (intro allI impI)
        fix env r st out
        assume h: "out \<in> set (pmatch_prog (Suc fuel) env r st)"
        show "consumes_prefix st out"
        proof (cases r)
          case (PAtom core)
          then show ?thesis
            using h pmatch_consumes_prefix by simp
        next
          case (PCall n)
          then show ?thesis
            using h pmIH by (cases "env n") auto
        next
          case (PProgSeq r1 r2)
          then obtain mid where
            mid: "mid \<in> set (pmatch_prog fuel env r1 st)"
            and out: "out \<in> set (pmatch_prog fuel env r2 mid)"
            using h by auto
          have "consumes_prefix st mid"
            using pmIH[OF mid] .
          moreover have "consumes_prefix mid out"
            using pmIH[OF out] .
          ultimately show ?thesis
            using consumes_prefix_trans by blast
        next
          case (PProgAlt r1 r2)
          then show ?thesis
            using h pmIH by auto
        next
          case (PProgAtomic r)
          then have "out \<in> set (pmatch_prog fuel env r st)"
            using h first_only_subset by auto
          then show ?thesis
            using pmIH by blast
        next
          case (PProgQuant q lo hi r)
          then show ?thesis
            using h qmIH by simp
        qed
      qed
      show "\<forall>env q lo hi r st out.
        out \<in> set (qmatch_prog (Suc fuel) env q lo hi r st) \<longrightarrow> consumes_prefix st out"
      proof (intro allI impI)
        fix env q lo hi r st out
        assume h: "out \<in> set (qmatch_prog (Suc fuel) env q lo hi r st)"
        show "consumes_prefix st out"
        proof (cases "0 < lo")
          case True
          show ?thesis
          proof (cases "can_take hi")
            case False
            then show ?thesis
              using h True by simp
          next
            case True
            from h \<open>0 < lo\<close> True obtain mid where
              mid: "mid \<in> set (progress_outputs st (pmatch_prog fuel env r st))"
              and out: "out \<in> set (qmatch_prog fuel env q (lo - 1) (dec_bound hi) r mid)"
              by (auto simp add: progress_outputs_def)
            have "consumes_prefix st mid"
              using mid pmIH progress_outputs_subset by blast
            moreover have "consumes_prefix mid out"
              using qmIH[OF out] .
            ultimately show ?thesis
              using consumes_prefix_trans by blast
          qed
        next
          case False
          then have lo0: "lo = 0" by simp
          show ?thesis
          proof (cases "can_take hi")
            case False
            then show ?thesis
              using h lo0 by simp
          next
            case True
            let ?next = "progress_outputs st (pmatch_prog fuel env r st)"
            show ?thesis
            proof (cases q)
              case Greedy
              then consider
                (stop) "out = st" |
                (more) mid where
                  "mid \<in> set ?next"
                  "out \<in> set (qmatch_prog fuel env Greedy 0 (dec_bound hi) r mid)"
                using h lo0 True by (auto simp add: Let_def)
              then show ?thesis
              proof cases
                case stop
                then show ?thesis by simp
              next
                case (more mid)
                have "consumes_prefix st mid"
                  using more(1) pmIH progress_outputs_subset by blast
                moreover have "consumes_prefix mid out"
                  using qmIH[OF more(2)] .
                ultimately show ?thesis
                  using consumes_prefix_trans by blast
              qed
            next
              case Lazy
              then consider
                (stop) "out = st" |
                (more) mid where
                  "mid \<in> set ?next"
                  "out \<in> set (qmatch_prog fuel env Lazy 0 (dec_bound hi) r mid)"
                using h lo0 True by (auto simp add: Let_def)
              then show ?thesis
              proof cases
                case stop
                then show ?thesis by simp
              next
                case (more mid)
                have "consumes_prefix st mid"
                  using more(1) pmIH progress_outputs_subset by blast
                moreover have "consumes_prefix mid out"
                  using qmIH[OF more(2)] .
                ultimately show ?thesis
                  using consumes_prefix_trans by blast
              qed
            next
              case Possessive
              show ?thesis
              proof (cases ?next)
                case Nil
                then show ?thesis
                  using h lo0 \<open>can_take hi\<close> Possessive by (simp add: Let_def)
              next
                case (Cons mid rest)
                then have mid: "mid \<in> set ?next"
                  by simp
                have out: "out \<in> set (qmatch_prog fuel env Possessive 0 (dec_bound hi) r mid)"
                  using h lo0 \<open>can_take hi\<close> Possessive Cons by (simp add: Let_def)
                have "consumes_prefix st mid"
                  using mid pmIH progress_outputs_subset by blast
                moreover have "consumes_prefix mid out"
                  using qmIH[OF out] .
                ultimately show ?thesis
                  using consumes_prefix_trans by blast
              qed
            next
              case Linear
              show ?thesis
              proof (cases ?next)
                case Nil
                then show ?thesis
                  using h lo0 \<open>can_take hi\<close> Linear by (simp add: Let_def)
              next
                case (Cons mid rest)
                then have mid: "mid \<in> set ?next"
                  by simp
                have out: "out \<in> set (qmatch_prog fuel env Linear 0 (dec_bound hi) r mid)"
                  using h lo0 \<open>can_take hi\<close> Linear Cons by (simp add: Let_def)
                have "consumes_prefix st mid"
                  using mid pmIH progress_outputs_subset by blast
                moreover have "consumes_prefix mid out"
                  using qmIH[OF out] .
                ultimately show ?thesis
                  using consumes_prefix_trans by blast
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  show "out \<in> set (pmatch_prog fuel env r st) \<Longrightarrow> consumes_prefix st out"
    using both by blast
  show "out \<in> set (qmatch_prog fuel env q lo hi r st) \<Longrightarrow> consumes_prefix st out"
    using both by blast
qed

lemma pmatch_prog_preserves_spine:
  assumes "out \<in> set (pmatch_prog fuel env r st)"
  shows "pleft out @ pright out = pleft st @ pright st"
proof -
  from pmatch_prog_consumes_prefix[OF assms] obtain w where
    "pleft out = pleft st @ w" "pright st = w @ pright out"
    by (auto simp add: consumes_prefix_def)
  then show ?thesis
    by simp
qed

lemma qmatch_prog_lazy_zero_order:
  assumes "can_take hi"
  shows "qmatch_prog (Suc fuel) env Lazy 0 hi r st =
    st # concat (map (qmatch_prog fuel env Lazy 0 (dec_bound hi) r)
      (progress_outputs st (pmatch_prog fuel env r st)))"
  using assms by (simp add: Let_def)

lemma qmatch_prog_greedy_zero_order:
  assumes "can_take hi"
  shows "qmatch_prog (Suc fuel) env Greedy 0 hi r st =
    concat (map (qmatch_prog fuel env Greedy 0 (dec_bound hi) r)
      (progress_outputs st (pmatch_prog fuel env r st))) @ [st]"
  using assms by (simp add: Let_def)

section \<open>Canonical PCRE behaviour examples\<close>

definition pcre_ex_alt_aba_ab_a :: pcre
where
  "pcre_ex_alt_aba_ab_a =
    PAlt
      (PSeq (PChar (CHR ''a'')) (PSeq (PChar (CHR ''b'')) (PChar (CHR ''a''))))
      (PAlt
        (PSeq (PChar (CHR ''a'')) (PChar (CHR ''b'')))
        (PChar (CHR ''a'')))"

definition pcre_ex_greedy_ababa :: pcre
where
  "pcre_ex_greedy_ababa =
    PSeq PStart (PSeq (PQuant Greedy 0 None pcre_ex_alt_aba_ab_a) PEnd)"

definition pcre_ex_possessive_ababa :: pcre
where
  "pcre_ex_possessive_ababa =
    PSeq PStart (PSeq (PQuant Possessive 0 None pcre_ex_alt_aba_ab_a) PEnd)"

text \<open>
  The two definitions above pin down the ASTs for the canonical Perl/PCRE
  smoke test.  The exact checked theorem pair is tracked as PCRE-001; it should
  be proved with a narrow proof script rather than whole-engine code
  evaluation, because the full matcher contains lookbehind equations whose
  generated-code path requires extra finite-enumeration infrastructure.
\<close>
end
