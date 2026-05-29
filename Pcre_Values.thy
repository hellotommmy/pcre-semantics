theory Pcre_Values
  imports Pcre_POC
begin

section \<open>PCRE submatch values\<close>

text \<open>
  This theory starts a value layer for PCRE-style matching.  It is deliberately
  small: the full regex inhabitation relation is not defined here yet, because
  atomic groups, possessive repetition, and assertion captures need an ordered
  engine-aware relation rather than an unordered language relation.
\<close>

datatype pval =
  PVoid
| PCharVal char
| PClassVal char
| PDotVal char
| PSeqVal pval pval
| PLeftVal pval
| PRightVal pval
| PRepVal qkind "pval list"
| PCaptureVal nat pval
| PBackrefVal nat string
| PAtomicVal pval
| PLookVal bool
| PLookBehindVal bool
| PCondYesVal pval
| PCondNoVal pval
| PAssertVal

primrec pflat :: "pval \<Rightarrow> string"
where
  "pflat PVoid = []"
| "pflat (PCharVal c) = [c]"
| "pflat (PClassVal c) = [c]"
| "pflat (PDotVal c) = [c]"
| "pflat (PSeqVal v1 v2) = pflat v1 @ pflat v2"
| "pflat (PLeftVal v) = pflat v"
| "pflat (PRightVal v) = pflat v"
| "pflat (PRepVal q vs) = concat (map pflat vs)"
| "pflat (PCaptureVal n v) = pflat v"
| "pflat (PBackrefVal n w) = w"
| "pflat (PAtomicVal v) = pflat v"
| "pflat (PLookVal positive) = []"
| "pflat (PLookBehindVal positive) = []"
| "pflat (PCondYesVal v) = pflat v"
| "pflat (PCondNoVal v) = pflat v"
| "pflat PAssertVal = []"

fun pcaps_after :: "pval \<Rightarrow> capenv \<Rightarrow> capenv"
and pcaps_after_list :: "pval list \<Rightarrow> capenv \<Rightarrow> capenv"
where
  "pcaps_after PVoid caps = caps"
| "pcaps_after (PCharVal c) caps = caps"
| "pcaps_after (PClassVal c) caps = caps"
| "pcaps_after (PDotVal c) caps = caps"
| "pcaps_after (PSeqVal v1 v2) caps =
    pcaps_after v2 (pcaps_after v1 caps)"
| "pcaps_after (PLeftVal v) caps = pcaps_after v caps"
| "pcaps_after (PRightVal v) caps = pcaps_after v caps"
| "pcaps_after (PRepVal q vs) caps =
    pcaps_after_list vs caps"
| "pcaps_after (PCaptureVal n v) caps =
    (pcaps_after v caps)(n := Some (pflat v))"
| "pcaps_after (PBackrefVal n w) caps = caps"
| "pcaps_after (PAtomicVal v) caps = pcaps_after v caps"
| "pcaps_after (PLookVal positive) caps = caps"
| "pcaps_after (PLookBehindVal positive) caps = caps"
| "pcaps_after (PCondYesVal v) caps = pcaps_after v caps"
| "pcaps_after (PCondNoVal v) caps = pcaps_after v caps"
| "pcaps_after PAssertVal caps = caps"
| "pcaps_after_list [] caps = caps"
| "pcaps_after_list (v # vs) caps = pcaps_after_list vs (pcaps_after v caps)"

definition pval_explains_state :: "pstate \<Rightarrow> pval \<Rightarrow> pstate \<Rightarrow> bool"
where
  "pval_explains_state st v out \<longleftrightarrow>
    pleft out = pleft st @ pflat v \<and>
    pright st = pflat v @ pright out \<and>
    pcaps out = pcaps_after v (pcaps st)"

lemma pval_explains_state_spine:
  assumes "pval_explains_state st v out"
  shows "pleft out @ pright out = pleft st @ pright st"
proof -
  have left: "pleft out = pleft st @ pflat v"
    using assms by (simp add: pval_explains_state_def)
  have right: "pright st = pflat v @ pright out"
    using assms by (simp add: pval_explains_state_def)
  show ?thesis
    by (simp add: left right)
qed

lemma pval_explains_state_consumes_prefix:
  assumes "pval_explains_state st v out"
  shows "consumes_prefix st out"
  using assms
  by (auto simp add: pval_explains_state_def consumes_prefix_def)

lemma pval_explains_state_caps:
  assumes "pval_explains_state st v out"
  shows "pcaps out = pcaps_after v (pcaps st)"
  using assms by (simp add: pval_explains_state_def)

lemma pval_explains_stateI:
  assumes "pleft out = pleft st @ pflat v"
    and "pright st = pflat v @ pright out"
    and "pcaps out = pcaps_after v (pcaps st)"
  shows "pval_explains_state st v out"
  using assms by (simp add: pval_explains_state_def)

lemma pcaps_after_seq [simp]:
  "pcaps_after (PSeqVal v1 v2) caps =
    pcaps_after v2 (pcaps_after v1 caps)"
  by simp

lemma pcaps_after_capture [simp]:
  "pcaps_after (PCaptureVal n v) caps =
    (pcaps_after v caps)(n := Some (pflat v))"
  by simp

lemma pflat_rep_append [simp]:
  "pflat (PRepVal q (xs @ ys)) =
    pflat (PRepVal q xs) @ pflat (PRepVal q ys)"
  by simp

lemma pcaps_after_list_append [simp]:
  "pcaps_after_list (xs @ ys) caps =
    pcaps_after_list ys (pcaps_after_list xs caps)"
  by (induct xs arbitrary: caps) simp_all

lemma pcaps_after_rep_append [simp]:
  "pcaps_after (PRepVal q (xs @ ys)) caps =
    pcaps_after (PRepVal q ys) (pcaps_after (PRepVal q xs) caps)"
  by simp

lemma pval_explains_state_void [simp]:
  "pval_explains_state st PVoid st"
  by (simp add: pval_explains_state_def)

lemma pval_explains_state_assert [simp]:
  "pval_explains_state st PAssertVal st"
  by (simp add: pval_explains_state_def)

lemma pval_explains_state_look [simp]:
  "pval_explains_state st (PLookVal positive) st"
  by (simp add: pval_explains_state_def)

lemma pval_explains_state_lookbehind [simp]:
  "pval_explains_state st (PLookBehindVal positive) st"
  by (simp add: pval_explains_state_def)

lemma pval_explains_state_char:
  "pval_explains_state
    (PState l (c # s) caps)
    (PCharVal c)
    (PState (l @ [c]) s caps)"
  by (simp add: pval_explains_state_def)

lemma pval_explains_state_class:
  "pval_explains_state
    (PState l (c # s) caps)
    (PClassVal c)
    (PState (l @ [c]) s caps)"
  by (simp add: pval_explains_state_def)

lemma pval_explains_state_dot:
  "pval_explains_state
    (PState l (c # s) caps)
    (PDotVal c)
    (PState (l @ [c]) s caps)"
  by (simp add: pval_explains_state_def)

lemma pval_explains_state_seq:
  assumes left: "pval_explains_state st v1 mid"
    and right: "pval_explains_state mid v2 out"
  shows "pval_explains_state st (PSeqVal v1 v2) out"
proof (rule pval_explains_stateI)
  show "pleft out = pleft st @ pflat (PSeqVal v1 v2)"
    using left right by (simp add: pval_explains_state_def append_assoc)
  show "pright st = pflat (PSeqVal v1 v2) @ pright out"
    using left right by (simp add: pval_explains_state_def append_assoc)
  show "pcaps out = pcaps_after (PSeqVal v1 v2) (pcaps st)"
    using left right by (simp add: pval_explains_state_def)
qed

lemma pval_explains_state_left:
  assumes "pval_explains_state st v out"
  shows "pval_explains_state st (PLeftVal v) out"
  using assms by (simp add: pval_explains_state_def)

lemma pval_explains_state_right:
  assumes "pval_explains_state st v out"
  shows "pval_explains_state st (PRightVal v) out"
  using assms by (simp add: pval_explains_state_def)

lemma pval_explains_state_atomic:
  assumes "pval_explains_state st v out"
  shows "pval_explains_state st (PAtomicVal v) out"
  using assms by (simp add: pval_explains_state_def)

lemma pval_explains_state_cond_yes:
  assumes "pval_explains_state st v out"
  shows "pval_explains_state st (PCondYesVal v) out"
  using assms by (simp add: pval_explains_state_def)

lemma pval_explains_state_cond_no:
  assumes "pval_explains_state st v out"
  shows "pval_explains_state st (PCondNoVal v) out"
  using assms by (simp add: pval_explains_state_def)

lemma pval_explains_state_capture:
  assumes "pval_explains_state (PState l s caps) v (PState l' s' caps')"
  shows "pval_explains_state
    (PState l s caps)
    (PCaptureVal n v)
    (PState l' s' (caps'(n := Some (pflat v))))"
  using assms by (simp add: pval_explains_state_def)

lemma pval_explains_state_backref:
  assumes "starts_with w s"
  shows "pval_explains_state
    (PState l s caps)
    (PBackrefVal n w)
    (PState (l @ w) (drop (length w) s) caps)"
proof (rule pval_explains_stateI)
  show "pleft (PState (l @ w) (drop (length w) s) caps) =
    pleft (PState l s caps) @ pflat (PBackrefVal n w)"
    by simp
  show "pright (PState l s caps) =
    pflat (PBackrefVal n w) @ pright (PState (l @ w) (drop (length w) s) caps)"
    using starts_with_drop[OF assms] by simp
  show "pcaps (PState (l @ w) (drop (length w) s) caps) =
    pcaps_after (PBackrefVal n w) (pcaps (PState l s caps))"
    by simp
qed

end
