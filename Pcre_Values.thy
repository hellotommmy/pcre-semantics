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

section \<open>Core value inhabitation\<close>

text \<open>
  This relation covers the core state-indexed fragment whose value behaviour is
  not affected by ordered repetition or atomic commitment.  Quantifiers,
  atomic groups, and lookaround are intentionally left for later relations.
\<close>

fun pcore_supported :: "pcre \<Rightarrow> bool"
where
  "pcore_supported PFail = True"
| "pcore_supported PEps = True"
| "pcore_supported (PChar c) = True"
| "pcore_supported (PClass C) = True"
| "pcore_supported (PDot excluded) = True"
| "pcore_supported (PSeq r1 r2) = (pcore_supported r1 \<and> pcore_supported r2)"
| "pcore_supported (PAlt r1 r2) = (pcore_supported r1 \<and> pcore_supported r2)"
| "pcore_supported (PQuant q lo hi r) = False"
| "pcore_supported (PCapture n r) = pcore_supported r"
| "pcore_supported (PBackref n) = True"
| "pcore_supported (PAtomic r) = False"
| "pcore_supported (PLook positive r) = False"
| "pcore_supported (PLookBehind positive r) = False"
| "pcore_supported (PCond n yes no) = (pcore_supported yes \<and> pcore_supported no)"
| "pcore_supported (PWordBoundary W positive) = True"
| "pcore_supported (PLineStart NL) = True"
| "pcore_supported (PLineEnd NL) = True"
| "pcore_supported PStart = True"
| "pcore_supported PEnd = True"

fun pmonctx_core_supported :: "pmonctx \<Rightarrow> bool"
where
  "pmonctx_core_supported PMHole = True"
| "pmonctx_core_supported (PMSeqLeft C tail) =
    (pmonctx_core_supported C \<and> pcore_supported tail)"
| "pmonctx_core_supported (PMSeqRight prefix C) =
    (pcore_supported prefix \<and> pmonctx_core_supported C)"
| "pmonctx_core_supported (PMAltLeft C other) =
    (pmonctx_core_supported C \<and> pcore_supported other)"
| "pmonctx_core_supported (PMAltRight other C) =
    (pcore_supported other \<and> pmonctx_core_supported C)"
| "pmonctx_core_supported (PMCapture n C) =
    pmonctx_core_supported C"

lemma pcore_supported_plug_mon_context:
  assumes "pmonctx_core_supported C"
    and "pcore_supported r"
  shows "pcore_supported (plug_mon_context C r)"
  using assms by (induct C) simp_all

inductive pval_core_trace :: "pcre \<Rightarrow> pstate \<Rightarrow> pval \<Rightarrow> pstate \<Rightarrow> bool"
where
  Core_Eps:
    "pval_core_trace PEps st PVoid st"
| Core_Char:
    "pval_core_trace
      (PChar c)
      (PState l (c # s) caps)
      (PCharVal c)
      (PState (l @ [c]) s caps)"
| Core_Class:
    "c \<in> C \<Longrightarrow>
     pval_core_trace
      (PClass C)
      (PState l (c # s) caps)
      (PClassVal c)
      (PState (l @ [c]) s caps)"
| Core_Dot:
    "c \<notin> excluded \<Longrightarrow>
     pval_core_trace
      (PDot excluded)
      (PState l (c # s) caps)
      (PDotVal c)
      (PState (l @ [c]) s caps)"
| Core_Seq:
    "\<lbrakk>pval_core_trace r1 st v1 mid;
      pval_core_trace r2 mid v2 out\<rbrakk> \<Longrightarrow>
     pval_core_trace (PSeq r1 r2) st (PSeqVal v1 v2) out"
| Core_Alt_Left:
    "pval_core_trace r1 st v out \<Longrightarrow>
     pval_core_trace (PAlt r1 r2) st (PLeftVal v) out"
| Core_Alt_Right:
    "pval_core_trace r2 st v out \<Longrightarrow>
     pval_core_trace (PAlt r1 r2) st (PRightVal v) out"
| Core_Capture:
    "pval_core_trace r (PState l s caps) v (PState l' s' caps') \<Longrightarrow>
     pval_core_trace
      (PCapture n r)
      (PState l s caps)
      (PCaptureVal n v)
      (PState l' s' (caps'(n := Some (pflat v))))"
| Core_Backref:
    "\<lbrakk>caps n = Some w; starts_with w s\<rbrakk> \<Longrightarrow>
     pval_core_trace
      (PBackref n)
      (PState l s caps)
      (PBackrefVal n w)
      (PState (l @ w) (drop (length w) s) caps)"
| Core_Cond_Yes:
    "\<lbrakk>caps n = Some w;
      pval_core_trace yes (PState l s caps) v out\<rbrakk> \<Longrightarrow>
     pval_core_trace (PCond n yes no) (PState l s caps) (PCondYesVal v) out"
| Core_Cond_No:
    "\<lbrakk>caps n = None;
      pval_core_trace no (PState l s caps) v out\<rbrakk> \<Longrightarrow>
     pval_core_trace (PCond n yes no) (PState l s caps) (PCondNoVal v) out"
| Core_WordBoundary:
    "word_boundary W l s = positive \<Longrightarrow>
     pval_core_trace
      (PWordBoundary W positive)
      (PState l s caps)
      PAssertVal
      (PState l s caps)"
| Core_LineStart:
    "line_start NL l \<Longrightarrow>
     pval_core_trace
      (PLineStart NL)
      (PState l s caps)
      PAssertVal
      (PState l s caps)"
| Core_LineEnd:
    "line_end NL s \<Longrightarrow>
     pval_core_trace
      (PLineEnd NL)
      (PState l s caps)
      PAssertVal
      (PState l s caps)"
| Core_Start:
    "pval_core_trace
      PStart
      (PState [] s caps)
      PAssertVal
      (PState [] s caps)"
| Core_End:
    "pval_core_trace
      PEnd
      (PState l [] caps)
      PAssertVal
      (PState l [] caps)"

lemma pval_core_trace_explains_state:
  assumes "pval_core_trace r st v out"
  shows "pval_explains_state st v out"
  using assms
proof induction
  case (Core_Eps st)
  then show ?case by simp
next
  case (Core_Char c l s caps)
  then show ?case by (rule pval_explains_state_char)
next
  case (Core_Class c C l s caps)
  show ?case by (rule pval_explains_state_class)
next
  case (Core_Dot c excluded l s caps)
  show ?case by (rule pval_explains_state_dot)
next
  case (Core_Seq r1 st v1 mid r2 v2 out)
  then show ?case
    using pval_explains_state_seq by blast
next
  case (Core_Alt_Left r1 st v out r2)
  then show ?case
    using pval_explains_state_left by blast
next
  case (Core_Alt_Right r2 st v out r1)
  then show ?case
    using pval_explains_state_right by blast
next
  case (Core_Capture r l s caps v l' s' caps' n)
  then show ?case
    using pval_explains_state_capture by blast
next
  case (Core_Backref caps n w s l)
  then show ?case
    using pval_explains_state_backref by blast
next
  case (Core_Cond_Yes caps n w yes l s v out no)
  then show ?case
    using pval_explains_state_cond_yes by blast
next
  case (Core_Cond_No caps n no l s v out yes)
  then show ?case
    using pval_explains_state_cond_no by blast
next
  case (Core_WordBoundary W l s positive caps)
  then show ?case by simp
next
  case (Core_LineStart NL l s caps)
  then show ?case by simp
next
  case (Core_LineEnd NL s l caps)
  then show ?case by simp
next
  case (Core_Start s caps)
  then show ?case by simp
next
  case (Core_End l caps)
  then show ?case by simp
qed

lemma pval_core_trace_consumes_prefix:
  assumes "pval_core_trace r st v out"
  shows "consumes_prefix st out"
  using pval_core_trace_explains_state[OF assms]
    pval_explains_state_consumes_prefix
  by blast

lemma pval_core_trace_spine:
  assumes "pval_core_trace r st v out"
  shows "pleft out @ pright out = pleft st @ pright st"
  using pval_core_trace_explains_state[OF assms]
    pval_explains_state_spine
  by blast

section \<open>Fuelled core value runs\<close>

text \<open>
  The fuelled relation mirrors the executable matcher's fuel discipline.  It is
  intended as the first bridge from structured values back to `pmatch`.
\<close>

inductive pval_core_run ::
  "nat \<Rightarrow> pcre \<Rightarrow> pstate \<Rightarrow> pval \<Rightarrow> pstate \<Rightarrow> bool"
where
  CoreRun_Eps:
    "pval_core_run (Suc fuel) PEps st PVoid st"
| CoreRun_Char:
    "pval_core_run
      (Suc fuel)
      (PChar c)
      (PState l (c # s) caps)
      (PCharVal c)
      (PState (l @ [c]) s caps)"
| CoreRun_Class:
    "c \<in> C \<Longrightarrow>
     pval_core_run
      (Suc fuel)
      (PClass C)
      (PState l (c # s) caps)
      (PClassVal c)
      (PState (l @ [c]) s caps)"
| CoreRun_Dot:
    "c \<notin> excluded \<Longrightarrow>
     pval_core_run
      (Suc fuel)
      (PDot excluded)
      (PState l (c # s) caps)
      (PDotVal c)
      (PState (l @ [c]) s caps)"
| CoreRun_Seq:
    "\<lbrakk>pval_core_run fuel r1 st v1 mid;
      pval_core_run fuel r2 mid v2 out\<rbrakk> \<Longrightarrow>
     pval_core_run (Suc fuel) (PSeq r1 r2) st (PSeqVal v1 v2) out"
| CoreRun_Alt_Left:
    "pval_core_run fuel r1 st v out \<Longrightarrow>
     pval_core_run (Suc fuel) (PAlt r1 r2) st (PLeftVal v) out"
| CoreRun_Alt_Right:
    "pval_core_run fuel r2 st v out \<Longrightarrow>
     pval_core_run (Suc fuel) (PAlt r1 r2) st (PRightVal v) out"
| CoreRun_Capture:
    "pval_core_run fuel r (PState l s caps) v (PState l' s' caps') \<Longrightarrow>
     pval_core_run
      (Suc fuel)
      (PCapture n r)
      (PState l s caps)
      (PCaptureVal n v)
      (PState l' s' (caps'(n := Some (pflat v))))"
| CoreRun_Backref:
    "\<lbrakk>caps n = Some w; starts_with w s\<rbrakk> \<Longrightarrow>
     pval_core_run
      (Suc fuel)
      (PBackref n)
      (PState l s caps)
      (PBackrefVal n w)
      (PState (l @ w) (drop (length w) s) caps)"
| CoreRun_Cond_Yes:
    "\<lbrakk>caps n = Some w;
      pval_core_run fuel yes (PState l s caps) v out\<rbrakk> \<Longrightarrow>
     pval_core_run (Suc fuel) (PCond n yes no) (PState l s caps)
      (PCondYesVal v) out"
| CoreRun_Cond_No:
    "\<lbrakk>caps n = None;
      pval_core_run fuel no (PState l s caps) v out\<rbrakk> \<Longrightarrow>
     pval_core_run (Suc fuel) (PCond n yes no) (PState l s caps)
      (PCondNoVal v) out"
| CoreRun_WordBoundary:
    "word_boundary W l s = positive \<Longrightarrow>
     pval_core_run
      (Suc fuel)
      (PWordBoundary W positive)
      (PState l s caps)
      PAssertVal
      (PState l s caps)"
| CoreRun_LineStart:
    "line_start NL l \<Longrightarrow>
     pval_core_run
      (Suc fuel)
      (PLineStart NL)
      (PState l s caps)
      PAssertVal
      (PState l s caps)"
| CoreRun_LineEnd:
    "line_end NL s \<Longrightarrow>
     pval_core_run
      (Suc fuel)
      (PLineEnd NL)
      (PState l s caps)
      PAssertVal
      (PState l s caps)"
| CoreRun_Start:
    "pval_core_run
      (Suc fuel)
      PStart
      (PState [] s caps)
      PAssertVal
      (PState [] s caps)"
| CoreRun_End:
    "pval_core_run
      (Suc fuel)
      PEnd
      (PState l [] caps)
      PAssertVal
      (PState l [] caps)"

lemma pval_core_run_trace:
  assumes "pval_core_run fuel r st v out"
  shows "pval_core_trace r st v out"
  using assms
proof induction
  case (CoreRun_Eps fuel st)
  then show ?case by (rule Core_Eps)
next
  case (CoreRun_Char fuel c l s caps)
  then show ?case by (rule Core_Char)
next
  case (CoreRun_Class c C fuel l s caps)
  then show ?case by (rule Core_Class)
next
  case (CoreRun_Dot c excluded fuel l s caps)
  then show ?case by (rule Core_Dot)
next
  case (CoreRun_Seq fuel r1 st v1 mid r2 v2 out)
  show ?case
    using CoreRun_Seq.IH(1) CoreRun_Seq.IH(2) by (rule Core_Seq)
next
  case (CoreRun_Alt_Left fuel r1 st v out r2)
  show ?case
    using CoreRun_Alt_Left.IH by (rule Core_Alt_Left)
next
  case (CoreRun_Alt_Right fuel r2 st v out r1)
  show ?case
    using CoreRun_Alt_Right.IH by (rule Core_Alt_Right)
next
  case (CoreRun_Capture fuel r l s caps v l' s' caps' n)
  show ?case
    using CoreRun_Capture.IH by (rule Core_Capture)
next
  case (CoreRun_Backref caps n w s fuel l)
  show ?case
    using CoreRun_Backref.hyps by (rule Core_Backref)
next
  case (CoreRun_Cond_Yes caps n w fuel yes l s v out no)
  show ?case
    using CoreRun_Cond_Yes.hyps(1) CoreRun_Cond_Yes.IH by (rule Core_Cond_Yes)
next
  case (CoreRun_Cond_No caps n fuel no l s v out yes)
  show ?case
    using CoreRun_Cond_No.hyps(1) CoreRun_Cond_No.IH by (rule Core_Cond_No)
next
  case (CoreRun_WordBoundary W l s positive fuel caps)
  show ?case
    using CoreRun_WordBoundary.hyps by (rule Core_WordBoundary)
next
  case (CoreRun_LineStart NL l fuel s caps)
  show ?case
    using CoreRun_LineStart.hyps by (rule Core_LineStart)
next
  case (CoreRun_LineEnd NL s fuel l caps)
  show ?case
    using CoreRun_LineEnd.hyps by (rule Core_LineEnd)
next
  case (CoreRun_Start fuel s caps)
  then show ?case by (rule Core_Start)
next
  case (CoreRun_End fuel l caps)
  then show ?case by (rule Core_End)
qed

lemma pval_core_run_explains_state:
  assumes "pval_core_run fuel r st v out"
  shows "pval_explains_state st v out"
  using pval_core_trace_explains_state pval_core_run_trace assms by blast

lemma pval_core_run_sound_pmatch:
  assumes "pval_core_run fuel r st v out"
  shows "out \<in> set (pmatch fuel r st)"
  using assms
proof induction
  case (CoreRun_Eps fuel st)
  then show ?case by simp
next
  case (CoreRun_Char fuel c l s caps)
  then show ?case by simp
next
  case (CoreRun_Class c C fuel l s caps)
  then show ?case by simp
next
  case (CoreRun_Dot c excluded fuel l s caps)
  then show ?case by simp
next
  case (CoreRun_Seq fuel r1 st v1 mid r2 v2 out)
  have mid: "mid \<in> set (pmatch fuel r1 st)"
    using CoreRun_Seq.IH(1) .
  have out: "out \<in> set (pmatch fuel r2 mid)"
    using CoreRun_Seq.IH(2) .
  then have "out \<in> set (concat (map (pmatch fuel r2) (pmatch fuel r1 st)))"
    using mid by auto
  then show ?case by simp
next
  case (CoreRun_Alt_Left fuel r1 st v out r2)
  then show ?case by simp
next
  case (CoreRun_Alt_Right fuel r2 st v out r1)
  then show ?case by simp
next
  case (CoreRun_Capture fuel r l s caps v l' s' caps' n)
  have inner: "PState l' s' caps' \<in> set (pmatch fuel r (PState l s caps))"
    using CoreRun_Capture.IH .
  have explains: "pval_explains_state (PState l s caps) v (PState l' s' caps')"
    using pval_core_run_explains_state CoreRun_Capture.hyps by blast
  then have cap_text: "drop (length l) l' = pflat v"
    by (simp add: pval_explains_state_def)
  have mapped:
    "capture_update n l (PState l' s' caps') =
      PState l' s' (caps'(n := Some (pflat v)))"
    using cap_text by (simp add: capture_update_def)
  have img:
    "capture_update n l (PState l' s' caps') \<in>
      capture_update n l ` set (pmatch fuel r (PState l s caps))"
    using inner by (rule imageI)
  show ?case
    using img mapped by simp
next
  case (CoreRun_Backref caps n w s fuel l)
  then show ?case by simp
next
  case (CoreRun_Cond_Yes caps n w fuel yes l s v out no)
  then show ?case by simp
next
  case (CoreRun_Cond_No caps n fuel no l s v out yes)
  then show ?case by simp
next
  case (CoreRun_WordBoundary W l s positive fuel caps)
  then show ?case by simp
next
  case (CoreRun_LineStart NL l fuel s caps)
  then show ?case by simp
next
  case (CoreRun_LineEnd NL s fuel l caps)
  then show ?case by simp
next
  case (CoreRun_Start fuel s caps)
  then show ?case by simp
next
  case (CoreRun_End fuel l caps)
  then show ?case by simp
qed

lemma pmatch_core_run_complete:
  assumes "pcore_supported r"
    and "out \<in> set (pmatch fuel r st)"
  shows "\<exists>v. pval_core_run fuel r st v out"
  using assms
proof (induct fuel arbitrary: r st out)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  then have supported: "pcore_supported r"
    and out: "out \<in> set (pmatch (Suc fuel) r st)"
    by simp_all
  show ?case
  proof (cases r)
    case PFail
    then show ?thesis using out by simp
  next
    case PEps
    then show ?thesis
      using out CoreRun_Eps by auto
  next
    case (PChar c)
    then show ?thesis
    proof (cases st)
      case (PState l s caps)
      show ?thesis
      proof (cases s)
        case Nil
        then show ?thesis using out PChar PState by simp
      next
        case (Cons d rest)
        then have c_eq: "c = d" and out_eq: "out = PState (l @ [d]) rest caps"
          using out PChar PState by auto
        show ?thesis
        proof (intro exI)
          show "pval_core_run (Suc fuel) r st (PCharVal d) out"
            unfolding PChar PState Cons c_eq out_eq
            by (rule CoreRun_Char)
        qed
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
        then show ?thesis using out PClass PState by simp
      next
        case (Cons c rest)
        then have in_C: "c \<in> C" and out_eq: "out = PState (l @ [c]) rest caps"
          using out PClass PState by auto
        show ?thesis
        proof (intro exI)
          show "pval_core_run (Suc fuel) r st (PClassVal c) out"
            unfolding PClass PState Cons out_eq
            using in_C by (rule CoreRun_Class)
        qed
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
        then show ?thesis using out PDot PState by simp
      next
        case (Cons c rest)
        then have not_excluded: "c \<notin> excluded"
          and out_eq: "out = PState (l @ [c]) rest caps"
          using out PDot PState by auto
        show ?thesis
        proof (intro exI)
          show "pval_core_run (Suc fuel) r st (PDotVal c) out"
            unfolding PDot PState Cons out_eq
            using not_excluded by (rule CoreRun_Dot)
        qed
      qed
    qed
  next
    case (PSeq r1 r2)
    then have r1: "pcore_supported r1" and r2: "pcore_supported r2"
      using supported by simp_all
    from out PSeq obtain mid where
      mid: "mid \<in> set (pmatch fuel r1 st)"
      and out2: "out \<in> set (pmatch fuel r2 mid)"
      by auto
    obtain v1 where v1: "pval_core_run fuel r1 st v1 mid"
      using Suc.hyps[OF r1 mid] by blast
    obtain v2 where v2: "pval_core_run fuel r2 mid v2 out"
      using Suc.hyps[OF r2 out2] by blast
    then show ?thesis
      using CoreRun_Seq[OF v1 v2] PSeq by blast
  next
    case (PAlt r1 r2)
    then have r1: "pcore_supported r1" and r2: "pcore_supported r2"
      using supported by simp_all
    show ?thesis
    proof (cases "out \<in> set (pmatch fuel r1 st)")
      case True
      then obtain v where "pval_core_run fuel r1 st v out"
        using Suc.hyps[OF r1] by blast
      then show ?thesis
        using PAlt CoreRun_Alt_Left by blast
    next
      case False
      then have "out \<in> set (pmatch fuel r2 st)"
        using out PAlt by simp
      then obtain v where "pval_core_run fuel r2 st v out"
        using Suc.hyps[OF r2] by blast
      then show ?thesis
        using PAlt CoreRun_Alt_Right by blast
    qed
  next
    case (PQuant q lo hi r)
    then show ?thesis using supported by simp
  next
    case (PCapture n r)
    then show ?thesis
    proof (cases st)
      case (PState l s caps)
      from supported PCapture have rs: "pcore_supported r"
        by simp
      from out PCapture PState obtain mid where
        mid: "mid \<in> set (pmatch fuel r (PState l s caps))"
        and out_eq: "out = capture_update n l mid"
        by auto
      obtain l' s' caps' where mid_eq: "mid = PState l' s' caps'"
        by (cases mid)
      obtain v where v: "pval_core_run fuel r (PState l s caps) v (PState l' s' caps')"
        using Suc.hyps[OF rs] mid mid_eq by blast
      have explains: "pval_explains_state (PState l s caps) v (PState l' s' caps')"
        using pval_core_run_explains_state[OF v] .
      then have cap_text: "drop (length l) l' = pflat v"
        by (simp add: pval_explains_state_def)
      have out_shape: "out = PState l' s' (caps'(n := Some (pflat v)))"
        using out_eq mid_eq cap_text by (simp add: capture_update_def)
      show ?thesis
        using CoreRun_Capture[OF v, of n] out_shape PCapture PState by blast
    qed
  next
    case (PBackref n)
    then show ?thesis
    proof (cases st)
      case (PState l s caps)
      show ?thesis
      proof (cases "caps n")
        case None
        then show ?thesis using out PBackref PState by simp
      next
        case (Some w)
        then have sw: "starts_with w s"
          and out_eq: "out = PState (l @ w) (drop (length w) s) caps"
          using out PBackref PState by auto
        show ?thesis
        proof (intro exI)
          show "pval_core_run (Suc fuel) r st (PBackrefVal n w) out"
            unfolding PBackref PState out_eq
            using Some sw by (rule CoreRun_Backref)
        qed
      qed
    qed
  next
    case (PAtomic r)
    then show ?thesis using supported by simp
  next
    case (PLook positive r)
    then show ?thesis using supported by simp
  next
    case (PLookBehind positive r)
    then show ?thesis using supported by simp
  next
    case (PCond n yes no)
    then have yes: "pcore_supported yes" and no: "pcore_supported no"
      using supported by simp_all
    show ?thesis
    proof (cases st)
      case (PState l s caps)
      show ?thesis
      proof (cases "caps n")
        case None
        then have "out \<in> set (pmatch fuel no (PState l s caps))"
          using out PCond PState by simp
        then obtain v where "pval_core_run fuel no (PState l s caps) v out"
          using Suc.hyps[OF no] by blast
        then show ?thesis
          using None PCond PState CoreRun_Cond_No by blast
      next
        case (Some w)
        then have "out \<in> set (pmatch fuel yes (PState l s caps))"
          using out PCond PState by simp
        then obtain v where "pval_core_run fuel yes (PState l s caps) v out"
          using Suc.hyps[OF yes] by blast
        then show ?thesis
          using Some PCond PState CoreRun_Cond_Yes by blast
      qed
    qed
  next
    case (PWordBoundary W positive)
    then show ?thesis
    proof (cases st)
      case (PState l s caps)
      then have wb: "word_boundary W l s = positive"
        and out_eq: "out = PState l s caps"
        using out PWordBoundary by auto
      show ?thesis
      proof (intro exI)
        show "pval_core_run (Suc fuel) r st PAssertVal out"
          unfolding PWordBoundary PState out_eq
          using wb by (rule CoreRun_WordBoundary)
      qed
    qed
  next
    case (PLineStart NL)
    then show ?thesis
    proof (cases st)
      case (PState l s caps)
      then have ls: "line_start NL l"
        and out_eq: "out = PState l s caps"
        using out PLineStart by auto
      show ?thesis
      proof (intro exI)
        show "pval_core_run (Suc fuel) r st PAssertVal out"
          unfolding PLineStart PState out_eq
          using ls by (rule CoreRun_LineStart)
      qed
    qed
  next
    case (PLineEnd NL)
    then show ?thesis
    proof (cases st)
      case (PState l s caps)
      then have le: "line_end NL s"
        and out_eq: "out = PState l s caps"
        using out PLineEnd by auto
      show ?thesis
      proof (intro exI)
        show "pval_core_run (Suc fuel) r st PAssertVal out"
          unfolding PLineEnd PState out_eq
          using le by (rule CoreRun_LineEnd)
      qed
    qed
  next
    case PStart
    then show ?thesis
    proof (cases st)
      case (PState l s caps)
      then have l_nil: "l = []"
        and out_eq: "out = PState l s caps"
        using out PStart by auto
      show ?thesis
      proof (intro exI)
        show "pval_core_run (Suc fuel) r st PAssertVal out"
          unfolding PStart PState out_eq l_nil
          by (rule CoreRun_Start)
      qed
    qed
  next
    case PEnd
    then show ?thesis
    proof (cases st)
      case (PState l s caps)
      then have s_nil: "s = []"
        and out_eq: "out = PState l s caps"
        using out PEnd by auto
      show ?thesis
      proof (intro exI)
        show "pval_core_run (Suc fuel) r st PAssertVal out"
          unfolding PEnd PState out_eq s_nil
          by (rule CoreRun_End)
      qed
    qed
  qed
qed

lemma pmatch_mon_context_core_run_complete:
  assumes "pmonctx_core_supported C"
    and "pcore_supported r"
    and "out \<in> set (pmatch fuel (plug_mon_context C r) st)"
  shows "\<exists>v. pval_core_run fuel (plug_mon_context C r) st v out"
proof -
  have "pcore_supported (plug_mon_context C r)"
    using assms(1,2) by (rule pcore_supported_plug_mon_context)
  then show ?thesis
    using assms(3) by (rule pmatch_core_run_complete)
qed

end
