theory %invisible Quasi
imports Complex_Main
begin


section "Administrative Lemmas"

text {*
  We prove here general lemmas that will be needed in the following.
*}

lemma ntimes_suc_dist [simp]: 
  fixes T :: real
  shows "(Suc j) * T =  j * T + T"
  by (simp add: comm_semiring_class.distrib real_of_nat_Suc)

lemma ntimes_nzero_min [intro]:
  fixes T :: real and k::nat 
  shows "\<lbrakk> 0 \<le> T; 0 < k \<rbrakk> \<Longrightarrow> T \<le> k * T"
  by (metis Suc_leI monoid_mult_class.mult.right_neutral 
  mult.commute mult_left_mono real_of_nat_le_iff real_of_nat_one)

lemma ntimes_bound:
  fixes C :: real
  assumes "C > 0"
  shows "\<exists> k :: nat. k * C > D"
  using assms by (simp add: reals_Archimedean3)

lemma card1_x:
  assumes "card S = 1"
  and "x \<in> S"
  shows "S = {x}"
  proof - 
    from `card S = 1` `x \<in> S` have "card (S - {x}) = 0"
      by (metis One_nat_def card_Diff_singleton card_infinite diff_Suc_1 zero_neq_one)
    moreover from `card S = 1` have "finite S"
      by (metis One_nat_def Suc_not_Zero card_infinite)
    ultimately have "S - {x} = {}" by simp
    thus ?thesis
      using `x \<in> S` by (metis insert_Diff_single insert_absorb)
  qed

lemma card2_xyz:
  assumes "card S = 2"
  and "x \<in> S"
  and "y \<in> S"
  and "z \<in> S"
  and "x \<noteq> z"
  and "y \<noteq> z"
  shows "x = y"
  proof -
    from `card S = 2` `x \<in> S` have "card (S - {x}) = 1"
      by (metis Suc_1 Suc_not_Zero card_Diff_singleton card_infinite diff_Suc_1)
    moreover from `z \<in> S` `x \<noteq> z` have "z \<in> S - {x}" 
      by simp
    ultimately have "S - {x} = {z}" 
      by (simp add: card1_x)
    moreover from `x \<in> S` have "S = {x} \<union> (S - {x})" 
      by auto
    ultimately have "S = {x, z}" 
      by auto
    thus ?thesis 
      using `y \<in> S` `y \<noteq> z` by simp
  qed

lemma finite_max:
  fixes f :: "_ \<Rightarrow> nat"
  assumes "finite A"
  and "A \<noteq> {}"
  shows "\<exists> x \<in> A. f x = Max {f y | y. y \<in> A}"
  using assms(1-2) proof (induct)
  case insert
    fix x F
    assume "finite F"
    and "x \<notin> F" 
    and "F \<noteq> {} \<Longrightarrow> \<exists>x\<in>F. f x = Max {f y |y. y \<in> F}"
    and "insert x F \<noteq> {}"
    thus "\<exists> z \<in> insert x F. f z = Max {f y |y. y \<in> insert x F}"
    proof (cases "F = {}")
      assume "F = {}"
      hence "Max {f y | y. y \<in> insert x F} = Max {f y |y. y \<in> {x}}" 
        by simp
      hence "Max {f y | y. y \<in> insert x F} = f x" 
        by simp
      moreover have "x \<in> insert x F" 
        by simp
      ultimately have "f x = Max {f y |y. y \<in> insert x F}" 
        by simp
      thus ?thesis by simp
   next 
     assume "\<not> F = {}"
     with `(F \<noteq> {} \<Longrightarrow> \<exists>x\<in>F. f x = Max {f y |y. y \<in> F})` 
     obtain z 
     where "z \<in> F" 
     and "f z = Max {f y |y. y \<in> F}" 
       by auto
     thus ?thesis
     proof (cases "f x > f z")
       assume "f x > f z"
       with `f z = Max {f y |y. y \<in> F}`
         have "f x = max (f x) (Max {f y |y. y \<in> F})"
           by simp
       also have "... = Max (insert (f x) {f y |y. y \<in> F})"
         proof (rule Max_insert [symmetric])
           from `finite F` show "finite {f y |y. y \<in> F}" 
             by simp
         next
           from `\<not> F = {}` show "{f y |y. y \<in> F} \<noteq> {}" 
             by simp
         qed
       also have "... = Max (f ` insert x F)"
         by simp (metis Collect_mem_eq image_Collect)
       finally have "f x = Max (f ` insert x F)" .
       thus "\<exists>z\<in>insert x F. f z = Max {f y |y. y \<in> insert x F}"
         by (metis Collect_mem_eq image_Collect insertI1)
     next
       assume "\<not> f x > f z"
       with `f z = Max {f y |y. y \<in> F}`
         have "f z = max (f x) (Max {f y |y. y \<in> F})"
           by simp
       also have "... = Max (insert (f x) {f y |y. y \<in> F})"
         proof (rule Max_insert [symmetric])
           from `finite F` show "finite {f y |y. y \<in> F}" 
             by simp
         next
           from `\<not> F = {}` show "{f y |y. y \<in> F} \<noteq> {}" 
             by simp
         qed
       also have "... = Max (f ` insert x F)"
         by simp (metis Collect_mem_eq image_Collect)
       finally have "f z = Max (f ` insert x F)" .
       thus "\<exists>z\<in>insert x F. f z = Max {f y |y. y \<in> insert x F}"
         using `z \<in> F` by (metis Collect_mem_eq image_Collect insert_iff)
     qed
   qed
  qed (simp)



section "Preamble"

text {*
  In this section, we give the definitions of quasi-periodic systems and formalize 
  the happened before relation. Then we prove general lemmas on this relation.
*}

subsection "Global definitions"


(*
  Recommended abbreviations: (C-;)
    Tmin = T\<^sub>m\<^sub>i\<^sub>n
    Tmax = T\<^sub>m\<^sub>a\<^sub>x
    taumin = \<tau>\<^sub>m\<^sub>i\<^sub>n
    taumax = \<tau>\<^sub>m\<^sub>a\<^sub>x
    @@ = \<bullet>
*)

typedecl node

type_synonym time  = real
type_synonym delay = real
type_synonym communication = "node \<Rightarrow> node \<Rightarrow> bool"

record event =
  node :: node    (* node associated with event *)
  act  :: nat     (* sequential number of event *)

syntax
  "_event" :: "[node, nat] \<Rightarrow> event" ("_\<bullet>_" [1000, 1000] 1000)
translations
  "_event n i" \<rightleftharpoons> "\<lparr> node = n, act = i \<rparr>"

record tevent =
  date  :: time   (* time-stamp of an execution *)
  trans :: delay  (* the associated transmission delay *)

type_synonym trace = "event \<Rightarrow> tevent"

fun arrival :: "tevent \<Rightarrow> time"
  where "arrival te = date te + trans te"

fun step :: "event \<Rightarrow> event"
  where "step e = e\<lparr> act := act e + 1 \<rparr>"

inductive hb1 :: "trace \<Rightarrow> event \<Rightarrow> event \<Rightarrow> bool"
  for t :: trace
  where
    hb_subsequent: "\<And>A B i j. \<lbrakk> A = B; i < j \<rbrakk> \<Longrightarrow> hb1 t A\<bullet>i B\<bullet>j"
  | hb_arrival:    "\<And>e1 e2. \<lbrakk> arrival (t e1) \<le> date (t e2) \<rbrakk> \<Longrightarrow> hb1 t e1 e2"

lemmas hb1.cases [cases del]
lemma hb1_cases [elim!]: 
  "hb1 t A\<bullet>i B\<bullet>j \<Longrightarrow> 
   (A = B \<Longrightarrow> i < j \<Longrightarrow> P) \<Longrightarrow>
   (arrival (t A\<bullet>i) \<le> date (t B\<bullet>j) \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule hb1.cases) auto

syntax
  "_hb1" :: "[event, trace, event] \<Rightarrow> bool" ("_ \<mapsto>_ _" [100, 100, 100] 100)
translations
  "_hb1 e1 t e2" \<rightleftharpoons> "(CONST hb1 t e1 e2)"

syntax
  "_hb" :: "[event, trace, event] \<Rightarrow> bool" ("_ \<rightarrow>_ _" [100, 100, 100] 100)
translations
  "_hb e1 t e2" \<rightleftharpoons> "(CONST hb1 t)^++ e1 e2"

definition concur :: "trace \<Rightarrow> event \<Rightarrow> event \<Rightarrow> bool"
  where "concur t e1 e2 \<equiv> \<not> (e1 \<rightarrow>t e2) \<and> \<not> (e2 \<rightarrow>t e1)"

syntax
  "_concur" :: "[event, trace, event] \<Rightarrow> bool" ("_ \<parallel>_ _" [100, 100, 100] 100)
translations
  "_concur e1 t e2" \<rightleftharpoons> "(CONST concur t e1 e2)"

subsection "Quasi-periodic system"

locale quasiperiodic_system =
  fixes nodes :: "node set"
  and T\<^sub>m\<^sub>i\<^sub>n :: time
  and T\<^sub>m\<^sub>a\<^sub>x :: time
  and \<tau>\<^sub>m\<^sub>i\<^sub>n :: time
  and \<tau>\<^sub>m\<^sub>a\<^sub>x :: time
  and com :: communication

  assumes finnode: "finite nodes"
  and node_coherent: "\<forall>e:: event. node e \<in> nodes"
  and Tminpos: "0 < T\<^sub>m\<^sub>i\<^sub>n"
  and Tbounds: "T\<^sub>m\<^sub>i\<^sub>n \<le> T\<^sub>m\<^sub>a\<^sub>x"
  and tauminpos: "0 < \<tau>\<^sub>m\<^sub>i\<^sub>n"
  and taubounds: "\<tau>\<^sub>m\<^sub>i\<^sub>n \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
  and com_refl: "\<forall> N. com N N" 
begin


lemma Tminpos': "0 \<le> T\<^sub>m\<^sub>i\<^sub>n"
  using Tminpos by simp

lemma Tmaxpos : "0 < T\<^sub>m\<^sub>a\<^sub>x"
  using Tbounds Tminpos by simp

lemma Tmaxpos' : "0 \<le> T\<^sub>m\<^sub>a\<^sub>x"
  using Tbounds Tminpos' by simp

lemma tauminpos': "0 \<le> \<tau>\<^sub>m\<^sub>i\<^sub>n"
  using tauminpos by simp

lemma taumaxpos : "0 < \<tau>\<^sub>m\<^sub>a\<^sub>x"
  using taubounds tauminpos by simp

lemma taumaxpos' : "0 \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
  using taubounds tauminpos' by simp

definition quasiperiodic :: "trace \<Rightarrow> bool"
  where "quasiperiodic t = (\<forall>e.
      0 \<le> date (t e)
    \<and> T\<^sub>m\<^sub>i\<^sub>n \<le> date (t (step e)) - date (t e) 
    \<and> date (t (step e)) - date (t e) \<le> T\<^sub>m\<^sub>a\<^sub>x
    \<and> \<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans (t e) \<and> trans (t e) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x)"

lemma qp_step:
  assumes "quasiperiodic t"
  shows "T\<^sub>m\<^sub>i\<^sub>n \<le> date (t (step e)) - date (t e)
         \<and> date (t (step e)) - date (t e) \<le> T\<^sub>m\<^sub>a\<^sub>x"
  using assms unfolding quasiperiodic_def by (rule allE [where x="e"]) simp

lemma qp_suc:
  assumes "quasiperiodic t"
  shows "T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>(Suc i)) - date (t A\<bullet>i)
         \<and> date (t A\<bullet>(Suc i)) - date (t A\<bullet>i) \<le> T\<^sub>m\<^sub>a\<^sub>x"
  using qp_step [OF assms, where e="A\<bullet>i"] by simp

lemmas qp_suc_min = qp_suc [THEN conjunct1]
   and qp_suc_max = qp_suc [THEN conjunct2]

lemma qp_trans:
  assumes "quasiperiodic t"
  shows "\<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans (t e) \<and> trans (t e) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
  using assms unfolding quasiperiodic_def by (rule allE [where x="e"]) simp

lemma qp_cone_lower:
  assumes "quasiperiodic t"
  shows "k * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>(i + k)) - date (t A\<bullet>i)"
  proof (induct k)
    fix k
    assume "k * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>(i + k)) - date (t A\<bullet>i)" (is "_ \<le> ?fnik - ?fni")
    with `quasiperiodic t`
      have "T\<^sub>m\<^sub>i\<^sub>n + k * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>(Suc (i + k))) - ?fnik + (?fnik - ?fni)"
        by (rule add_mono [OF qp_suc_min])
    thus "(Suc k) * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>(i + Suc k)) - date (t A\<bullet>i)" 
       by (subst ntimes_suc_dist) simp
  qed (simp)

lemma qp_cone_lower_tmin:
  assumes qp: "quasiperiodic t"
  and "i < j"
  shows "date (t A\<bullet>i) + T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>j)"
  proof -
    from `i < j` obtain k 
    where "j = i + k" 
    and "0 < k"
      by (metis less_imp_add_positive)
    from this(2) have "T\<^sub>m\<^sub>i\<^sub>n \<le>  k * T\<^sub>m\<^sub>i\<^sub>n"
      by (rule ntimes_nzero_min [OF Tminpos'])
    hence "date (t A\<bullet>i) + T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>i) +  k * T\<^sub>m\<^sub>i\<^sub>n"
      by (rule add_left_mono)
    also have "date (t A\<bullet>i) + k * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>(i+k))"  
      using qp_cone_lower [OF qp, where k=k and i=i and A=A] by auto
    finally show "date (t A\<bullet>i) + T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>j)"
      using `j = i + k` by simp
  qed
    
lemma qp_cone_upper:
  assumes "quasiperiodic t"
  shows "date (t A\<bullet>(i + k)) - date (t A\<bullet>i) \<le> k * T\<^sub>m\<^sub>a\<^sub>x"
  proof (induct k)
    fix k
    assume "date (t A\<bullet>(i + k)) - date (t A\<bullet>i) \<le>  k * T\<^sub>m\<^sub>a\<^sub>x" (is "?fnik - ?fni \<le> _")
    with `quasiperiodic t`
      have "date (t A\<bullet>(Suc (i + k))) - ?fnik + (?fnik - ?fni) \<le> T\<^sub>m\<^sub>a\<^sub>x + k * T\<^sub>m\<^sub>a\<^sub>x"
        by (rule add_mono [OF qp_suc_max])
    thus "date (t A\<bullet>(i + Suc k)) - date (t A\<bullet>i) \<le> (Suc k) * T\<^sub>m\<^sub>a\<^sub>x"
      by (subst ntimes_suc_dist) simp
  qed (simp)

lemma qp_cone:
  assumes qp:"quasiperiodic t"
  and "i \<le> j"
  shows "(j - i) * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>j) - date (t A\<bullet>i) 
         \<and> date  (t A\<bullet>j) - date (t A\<bullet>i) \<le> (j - i) * T\<^sub>m\<^sub>a\<^sub>x" 
  proof -
    from `i \<le>j` have "i + (j - i) = j" 
      by simp 
    from `i \<le> j` obtain k 
    where "k \<ge> 0"
    and "k = j -i" 
      by simp     
    from qp `k \<ge>0` have "k * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>(i+k)) - date (t A\<bullet>i)"
      by (metis qp_cone_lower)
    with `i + (j - i) = j` have "(j - i) * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>j) - date (t A\<bullet>i)"
      using `k = j -i` by simp
    moreover from qp `k \<ge>0` have "date (t A\<bullet>(i+k)) - date (t A\<bullet>i) \<le> k * T\<^sub>m\<^sub>a\<^sub>x"
      by (metis qp_cone_upper)
    with `i + (j - i) = j` have "date (t A\<bullet>j) - date (t A\<bullet>i) \<le> (j-i) * T\<^sub>m\<^sub>a\<^sub>x"
      using `k = j -i` by simp
    ultimately  show ?thesis 
      using `i \<le> j` by (simp add:real_of_nat_diff)
  qed

lemma qp_date_ij:
  assumes qp: "quasiperiodic t"
  and "i \<noteq> j"
  and "date (t A\<bullet>i) \<le> date (t A\<bullet>j)"
  shows "i < j"
  proof (rule ccontr)
    assume "\<not> i < j"
    hence "i \<ge> j" 
      by simp
    hence "i > j" 
      using `i \<noteq> j` by simp
    hence "date (t A\<bullet>i) > date (t A\<bullet>j)"
      proof - 
        from qp `i>j` have "date (t A\<bullet>j) + T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>i)"
          by (rule qp_cone_lower_tmin)
        with Tminpos show ?thesis 
          by simp
      qed
    thus False 
      using `date (t A\<bullet>i) \<le> date (t A\<bullet>j)` by auto
  qed


subsection "Happened before"

lemma hb1_reasonable:
  assumes qp:"quasiperiodic t"
  and "e1 \<mapsto>t e2"
  shows "date (t e1) < date(t e2)"
  using assms(2) proof induct
    fix A B :: node 
    and i j :: nat
    assume "A = B"
    and "i < j"
    thus "date (t A\<bullet>i) < date(t B\<bullet>j)"
      proof -
        from qp `i<j` `A = B` have "date (t A\<bullet>i) +  T\<^sub>m\<^sub>i\<^sub>n \<le> date (t B\<bullet>j)" 
          by (simp add: qp_cone_lower_tmin)
        thus ?thesis 
          using Tminpos by simp
      qed
  next 
    fix e1 e2
    assume "arrival (t e1) \<le> date (t e2)"
    hence "date(t e1) + trans(t e1) \<le> date(t e2)" 
      by simp
    moreover have "\<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans(t e1)" 
      using qp qp_trans by simp
    ultimately show "date (t e1) < date (t e2)" 
      using tauminpos by simp
  qed

lemma hb_reasonable:
  assumes qp:"quasiperiodic t"
  and "e1 \<rightarrow>t e2"
  shows "date (t e1) < date(t e2)"
  using assms(2) proof induct
    fix y
    assume "e1 \<mapsto>t y"
    thus "date (t e1) < date (t y)"
      using qp by (simp add: hb1_reasonable)
  next
   fix y z 
   assume "e1 \<rightarrow>t y"
   and "y \<mapsto>t z"
   and "date (t e1) < date (t y)"
   thus "date (t e1) < date (t z)"
     using qp by (metis dual_order.strict_trans hb1_reasonable)
  qed

lemma hb_hb1_same:
  assumes qp:"quasiperiodic t"
  and "A\<bullet>i \<rightarrow>t A\<bullet>j"
  shows "A\<bullet>i \<mapsto>t A\<bullet>j"
  proof -
  from qp `A\<bullet>i \<rightarrow>t A\<bullet>j` have "date (t A\<bullet>i) < date (t A\<bullet>j)" 
    by (rule hb_reasonable)
  with qp have "i < j" 
    by (metis hb1_reasonable hb_subsequent less_asym linorder_neqE_nat)
  thus ?thesis 
    by (simp add: hb_subsequent)
  qed

lemma hb_A_ij:
  assumes qp:"quasiperiodic t" 
  and "A\<bullet>i \<rightarrow>t A\<bullet>j"
  shows "i < j"
  proof (rule ccontr)
    assume h:"\<not> i < j"
    from assms have "date (t A\<bullet>i) < date (t A\<bullet>j)" 
      by (rule hb_reasonable)
    show False
    proof (cases "i = j")
      assume "i = j"
      hence "date (t A\<bullet>i) = date (t A\<bullet>j)" 
        by simp
      thus False 
        using `date (t A\<bullet>i) < date (t A\<bullet>j)` by simp
    next 
      assume "\<not> i = j"
      with h have "i > j" by simp
      with qp have "date (t A\<bullet>i) > date (t A\<bullet>j)" 
        by (simp add: hb1_reasonable hb_subsequent)
      thus False 
        using `date (t A\<bullet>i) < date (t A\<bullet>j)` by simp
    qed
  qed
       
lemma hb_node:
  assumes "node x = node y"
  and "x \<noteq> y"
  shows "\<not> x \<parallel>t y"
  proof -
    from `node x = node y` obtain A i j 
    where "x = A\<bullet>i"
    and "y = A\<bullet>j"
      by (metis (full_types) event.surjective unit.exhaust)
    with `x \<noteq> y` have "i \<noteq> j" 
      by simp
    thus ?thesis
    proof (cases "i < j")
      assume "i < j"
      with `x = A\<bullet>i` `y = A\<bullet>j` have "x \<rightarrow>t y"
        by (simp add: hb_subsequent tranclp.r_into_trancl)
     thus ?thesis 
       using concur_def by simp
    next
      assume "\<not> i < j"
      with `i \<noteq> j` have "i > j" 
        by simp
      with  `x = A\<bullet>i` `y = A\<bullet>j` have "y \<rightarrow>t x"
        by (simp add: hb_subsequent tranclp.r_into_trancl)
      thus ?thesis 
        using concur_def by simp
    qed
  qed 

lemma hb_concur_nodes:
  assumes "(x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z)" 
  shows "node x \<noteq> node z \<and> node y \<noteq> node z"
  proof (rule ccontr)
    assume h:"\<not> (node x \<noteq> node z \<and> node y \<noteq> node z)"
    thus False 
    proof (cases "node x \<noteq> node z")
      assume "node x \<noteq> node z"
      with h have "node y = node z"
        by simp
      from assms have "y \<parallel>t z"
        by simp
      show ?thesis
      proof (cases "y = z")
        assume "y = z"
        moreover from assms have "x \<rightarrow>t y" 
          by simp
        ultimately  show ?thesis 
          using assms concur_def by simp
      next
        assume "\<not> y = z"
        with `node y = node z` have "\<not> y \<parallel>t z" 
          by (rule hb_node)
        with `y \<parallel>t z` show ?thesis 
          by simp
      qed
    next
      assume "\<not> node x \<noteq> node z"
      hence "node x = node z" 
        by simp
      from assms have "x \<parallel>t z" 
        by simp
      show ?thesis
      proof (cases "x = z")
        assume "x = z"
        moreover from assms have "x \<rightarrow>t y" 
          by simp
        ultimately  show ?thesis 
          using assms concur_def  by simp
      next
        assume "\<not> x = z"
        with `node x = node z` have "\<not> x \<parallel>t z" 
          by (rule hb_node)
        with `x \<parallel>t z` show ?thesis 
          by simp
      qed    
    qed
  qed


lemma hb_trans_arrival:
  assumes qp: "quasiperiodic t" 
  and "e1 \<rightarrow>t e2"
  shows "node e1 = node e2 \<or> 
      (\<exists> e. node e = node e1 
         \<and> date (t e) \<ge> date (t e1) 
         \<and> arrival (t e) \<le> date (t e2))"
  using assms(2) proof (induct)
  case base
   fix y
   assume "e1 \<mapsto>t y"
     thus "node e1 = node y \<or>  
           (\<exists>e. node e = node e1 
            \<and>  date (t e1) \<le> date (t e) 
            \<and> arrival (t e) \<le> date (t y))"
     proof (cases "node e1 = node y")
       assume "node e1 = node y"
       thus ?thesis 
         by simp
     next
       assume "\<not> node e1 = node y" 
       hence "arrival (t e1) \<le> date (t y)" 
         using `e1 \<mapsto>t y` by (metis event.select_convs(1) hb1.cases)
       moreover have "node e1 \<noteq> node y" 
         using `\<not> node e1 = node y` by simp
       ultimately show ?thesis 
         by auto
     qed
  next 
    case step
    fix y z
    assume "e1 \<rightarrow>t y"
    and "y \<mapsto>t z"
    and e1y:"node e1 = node y \<or> 
             (\<exists>e. node e = node e1 
              \<and> date (t e1) \<le> date (t e) 
              \<and> arrival (t e) \<le> date (t y))"
    thus e1z:"node e1 = node z \<or> 
              (\<exists>e. node e = node e1 
               \<and> date (t e1) \<le> date (t e) 
               \<and> arrival (t e) \<le> date (t z))"
    proof (cases "node e1 = node y")
      assume "\<not> node e1 = node y"
      then obtain e 
      where "arrival (t e) \<le> date (t y)" 
        using e1y by auto
      moreover have "date (t y) < date (t z)" 
        using `y \<mapsto>t z` qp by (simp add: hb1_reasonable)
      ultimately show ?thesis 
        using `node e1 \<noteq> node y` by (metis dual_order.trans e1y linear not_less)  
    next 
      assume "node e1 = node y"
      thus ?thesis
      proof (cases "\<not> node z = node y")
        assume "\<not> node z = node y"
        hence "arrival (t y) \<le> date (t z)" 
          using `y \<mapsto>t z` qp by (metis event.select_convs(1) hb1.cases)
        moreover have "date (t e1) < date (t y)" 
          using `e1 \<rightarrow>t y` qp by (simp add: hb_reasonable)
        ultimately show ?thesis 
          using `node e1 = node y` by auto
      next 
        assume "\<not>\<not> node z = node y"
        thus ?thesis 
          using `node e1 = node y` by simp
      qed         
    qed
  qed


lemma hb_trans:
  assumes qp:"quasiperiodic t"
  and "A\<bullet>i \<rightarrow>t B\<bullet>j"
  and "\<not> A\<bullet>i \<mapsto>t B\<bullet>j"
  shows "\<exists> k>i. A\<bullet>k \<mapsto>t B\<bullet>j"
  proof - 
    from assms(2-3) have "A \<noteq> B" 
      by (metis hb_hb1_same qp)
    then obtain e 
    where "node e = A" 
    and "date (t e) \<ge> date (t A\<bullet>i)" 
    and "arrival (t e) \<le> date (t B\<bullet>j)"
      using assms by (metis event.select_convs(1) hb_trans_arrival)
    from `node e = A` obtain k 
    where "e = A\<bullet>k" 
      by (metis (full_types) event.surjective unit.exhaust)
    hence "A\<bullet>k \<mapsto>t B\<bullet>j" 
      using `arrival (t e) \<le> date (t B\<bullet>j)` by (simp add: hb_arrival)
    from qp `\<not> A\<bullet>i \<mapsto>t B\<bullet>j` `A\<bullet>k \<mapsto>t B\<bullet>j` have "i \<noteq> k" 
      by auto
    moreover have "date (t A\<bullet>k) \<ge> date (t A\<bullet>i)"
      using `e = A\<bullet>k` `date (t e) \<ge> date (t A\<bullet>i)` by simp
    ultimately have "k>i" 
      using qp by (simp add: qp_date_ij)
    thus ?thesis 
      using `A\<bullet>k \<mapsto>t B\<bullet>j` by metis
  qed


subsection "The set of predecessors"

text {*
  We prove here that the set of predecessors of an event with respect to the relation 
  happened before is finite.
*}

lemma fin_Ai:
  assumes qp:"quasiperiodic t"
  shows "finite {A\<bullet>i | i. 0 \<le> i \<and> date (t A\<bullet>i) < D}"
  proof -
   from qp have "\<forall>i. i * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>i) - date (t A\<bullet>0)"
     by (metis monoid_add_class.add.left_neutral qp_cone_lower)
   moreover from qp have "date (t A\<bullet>0) \<ge> 0" 
     using quasiperiodic_def by simp
   hence "\<forall> i. date (t A\<bullet>i) - date (t A\<bullet>0) \<le> date (t A\<bullet>i)" 
     by simp
   ultimately have "\<forall>i. i * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>i)"
     by (metis dual_order.trans)
   from Tminpos obtain k :: nat 
   where "k * T\<^sub>m\<^sub>i\<^sub>n > D" 
     using ntimes_bound by auto
   with `\<forall>i. i * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>i)` have "k * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>k)" 
     by simp
   with `k * T\<^sub>m\<^sub>i\<^sub>n > D` have "date (t A\<bullet>k) > D" 
     by simp    
   hence "{A\<bullet>i | i. 0 \<le> i \<and> date (t A\<bullet>i) < D} \<subseteq> {A\<bullet>i | i. i < k}"
   proof -
     assume "D < date (t A\<bullet>k)"
     show "{A\<bullet>i | i. 0 \<le> i \<and> date (t A\<bullet>i) < D} \<subseteq> {A\<bullet>i | i. i < k}"
     proof 
       fix e
       assume "e \<in> {A\<bullet>i | i. 0 \<le> i \<and> date (t A\<bullet>i) < D}"
       then obtain j 
       where "0 \<le> j"
       and "date (t A\<bullet>j) < D"
       and "e = A\<bullet>j"  
         by auto
       with `D < date (t A\<bullet>k)` have "date (t A\<bullet>j) < date (t A\<bullet>k)" 
         by simp
       hence "date (t A\<bullet>j) \<le> date (t A\<bullet>k)" 
        by simp
       moreover have "j \<noteq> k"
       proof 
         assume "j = k"
         hence "j = k" 
           by simp
         hence "date (t A\<bullet>j) = date (t A\<bullet>k)" 
           by simp
         thus False 
           using `date (t A\<bullet>j) < date (t A\<bullet>k)` by simp
       qed
       ultimately have "j < k" 
         using qp by (simp add: qp_date_ij)
       with `e = A\<bullet>j` show "e \<in> {A\<bullet>i | i. i < k}" 
         by simp         
     qed
   qed
   moreover have "finite {A\<bullet>i | i. i < k}" 
     by simp
   ultimately show ?thesis 
     by (simp add: finite_subset)
  qed


lemma fin_node_date:
  assumes qp:"quasiperiodic t"
  shows "finite {e. node e = A \<and> date (t e) < D}"
  proof -
    have "{e. node e = A \<and> date (t e) < D} \<subseteq> {A\<bullet>i | i. 0 \<le> i \<and> date (t A\<bullet>i) < D}"
    proof
      fix e
      assume "e \<in> {e. node e = A \<and> date (t e) < D}"
      hence "node e = A" 
      and "date (t e) < D" 
        by auto
      then obtain j 
      where "0 \<le> j" 
      and "e = A\<bullet>j"
        by (metis (full_types) event.surjective le0 unit.exhaust)
      with `date (t e) < D` have "date (t A\<bullet>j) < D"
        by simp
      with `0 \<le> j` `e = A\<bullet>j` show "e \<in> {A\<bullet>i | i. 0 \<le> i \<and> date (t A\<bullet>i) < D}" 
        by simp
    qed
    moreover have "finite {A\<bullet>i | i. 0 \<le> i \<and> date (t A\<bullet>i) < D}" 
      using fin_Ai qp by simp
    ultimately show ?thesis
      by (metis (lifting, no_types) finite_subset)
  qed


lemma fin_date:
  assumes qp: "quasiperiodic t"
  shows "finite {e. date (t e) < D}" 
  proof -
   from qp have "\<forall> A. finite {e. node e = A \<and> date (t e) < D}" 
     by (simp add: fin_node_date)
   with finnode have "finite (\<Union>A \<in> nodes. {e. node e = A \<and> date (t e) < D})" 
     by simp
   moreover have "(\<Union>A \<in> nodes. {e. node e = A \<and> date (t e) < D}) = {e. date (t e) < D}"
   proof
     show "{e. date (t e) < D} \<subseteq> (\<Union>A \<in> nodes. {e. node e = A \<and> date (t e) < D})"
     proof
       fix e
       assume "e \<in> {e. date (t e) < D}"
       moreover from qp obtain A i 
       where "A \<in> nodes"
       and "e = A\<bullet>i" 
         by (metis event.cases event.select_convs(1) node_coherent)
       ultimately have "e \<in> {e. node e = A \<and> date (t e) < D}" 
         by auto
       thus "e \<in> (\<Union>A \<in> nodes. {e. node e = A \<and> date (t e) < D})"
         using `A \<in> nodes` by simp
     qed
     next 
       show "(\<Union>A \<in> nodes. {e. node e = A \<and> date (t e) < D}) \<subseteq> {e. date (t e) < D}"
       proof
         fix e
         assume "e \<in> (\<Union>A \<in> nodes. {e. node e = A \<and> date (t e) < D})"
         hence "date (t e) < D"
           by simp
         moreover have "e \<in> {e}" 
           by simp
         ultimately show "e \<in> {e. date (t e) < D}" 
           by simp
       qed     
   qed
   ultimately show ?thesis 
     by simp
  qed


lemma hb_finite:
  assumes qp: "quasiperiodic t"
  shows "finite {x. x \<rightarrow>t y}"
  proof -
    from qp have "\<forall>x \<in> {x. x \<rightarrow>t y}. date (t x) < date (t y)"
      by (simp add:hb_reasonable)
    hence "{x. x \<rightarrow>t y} \<subseteq> {x. date (t x) < date (t y)}" 
      by auto
    moreover with qp have "finite  {x. date (t x) < date (t y)}" 
      by (simp add: fin_date)
    ultimately show ?thesis
      by (rule finite_subset)
  qed


lemma hb_decr:
  assumes qp:"quasiperiodic t"
  and "x \<rightarrow>t y"
  shows "{z. z \<rightarrow>t x} \<subset> {x. x\<rightarrow>t y}"
  proof 
    show "{z. z \<rightarrow>t x} \<subseteq> {x. x\<rightarrow>t y}"
    proof 
      fix z
      assume "z \<in> {z. z \<rightarrow>t x}" 
      with `x \<rightarrow>t y` have "z \<rightarrow>t y" 
        by simp
      thus "z \<in> {x. x\<rightarrow>t y}" 
        by simp
    qed
  next 
    show "{z. z \<rightarrow>t x} \<noteq> {x. x\<rightarrow>t y}"
    proof -
      have "\<not> x \<rightarrow>t x"
      proof
        assume "x \<rightarrow>t x"
        with qp have "date (t x) < date (t x)"
          by (rule hb_reasonable)
        thus False 
          by simp
      qed
      hence "x \<notin> {z. z \<rightarrow>t x}" 
        by simp
      with `x \<rightarrow>t y` show "{z. z \<rightarrow>t x} \<noteq> {x. x\<rightarrow>t y}" 
        by auto
    qed
  qed


section "Happened Before and Real-Time"

text {*
  The following lemmas link the relation happened before and the real-time dates of events.
*}


lemma not_hb_realtime:
  assumes "quasiperiodic t"
  and "\<not>(e1 \<rightarrow>t e2)"
  and "node e1 \<noteq> node e2"
  shows "arrival (t e1) > date (t e2)"
  using assms by (metis hb_arrival leI tranclp.simps)

lemma hb_realtime_A:
  assumes qp:"quasiperiodic t"
  and "A\<bullet>i \<rightarrow>t A\<bullet>j"
  shows "(j - i) * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>j) - date (t A\<bullet>i) 
         \<and> date  (t A\<bullet>j) - date (t A\<bullet>i) \<le> (j - i) * T\<^sub>m\<^sub>a\<^sub>x"
  proof -
    from qp `A\<bullet>i \<rightarrow>t A\<bullet>j` have "i < j" 
      by (metis hb_A_ij)
    hence "i \<le> j" 
      by simp
    thus ?thesis 
      using qp  by (simp add: qp_cone)
  qed

lemma message_inversion:
  assumes qp:"quasiperiodic t"
  and "T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n > \<tau>\<^sub>m\<^sub>a\<^sub>x"
  shows "\<forall> C p q. p < q \<longrightarrow> arrival (t C\<bullet>p) < arrival (t C\<bullet>q)"
  proof (rule ccontr)
    assume "\<not> (\<forall> C p q. p < q \<longrightarrow> arrival (t C\<bullet>p) < arrival (t C\<bullet>q))"
    then obtain A i j 
    where "i < j"
    and "\<not>(arrival (t A\<bullet>i) < arrival (t A\<bullet>j))" 
      by auto
    hence h:"arrival (t A\<bullet>i) \<ge> arrival (t A\<bullet>j)" 
      by simp
    from qp obtain transmin: "\<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans (t A\<bullet>j)"
    and transmax: "trans (t A\<bullet>i) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
      using quasiperiodic_def by simp
    from transmin have arj:"date (t A\<bullet>j) + \<tau>\<^sub>m\<^sub>i\<^sub>n \<le> arrival (t A\<bullet>j)" 
      by simp
    from transmax have ari:"date (t A\<bullet>i) + \<tau>\<^sub>m\<^sub>a\<^sub>x \<ge> arrival (t A\<bullet>i)" 
      by simp
    from qp `i < j` have subs:"date (t A\<bullet>i) + T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>j)"
      by (rule qp_cone_lower_tmin)
    from arj h have "date (t A\<bullet>j) + \<tau>\<^sub>m\<^sub>i\<^sub>n \<le> arrival (t A\<bullet>i)" 
      by simp
    with ari have "date (t A\<bullet>j) + \<tau>\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>i) + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      by simp
    moreover from subs arj have "date (t A\<bullet>i) + T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>j) + \<tau>\<^sub>m\<^sub>i\<^sub>n" 
      by simp
    ultimately have "T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
      by simp
    thus False 
      using assms(2) by simp
  qed


lemma hb_realtime:
  assumes qp: "quasiperiodic t"
  and mi: "\<forall> C p q. p < q \<longrightarrow> arrival (t C\<bullet>p) < arrival (t C\<bullet>q)"
  and "A \<noteq> B"
  shows "arrival (t A\<bullet>i) \<le> date (t B\<bullet>j) \<longleftrightarrow> A\<bullet>i \<rightarrow>t B\<bullet>j"
  proof 
    assume "A\<bullet>i \<rightarrow>t B\<bullet>j"
    show "arrival (t A\<bullet>i) \<le> date (t B\<bullet>j)"
    proof (rule ccontr) 
      assume h: "\<not> arrival (t A\<bullet>i) \<le> date (t B\<bullet>j)"
      hence "\<not> A\<bullet>i \<mapsto>t B\<bullet>j" 
        using `A \<noteq> B` by (metis hb1_cases)
      then obtain k 
      where "i < k"
      and "A\<bullet>k \<mapsto>t B\<bullet>j" 
        using qp `A \<noteq> B` `A\<bullet>i \<rightarrow>t B\<bullet>j`  by (metis hb_trans)
      hence "arrival (t A\<bullet>k) \<le> date (t B\<bullet>j)" 
        using `A \<noteq> B` qp by (metis hb1_cases)
      hence "arrival (t A\<bullet>i) \<ge> arrival (t A\<bullet>k)" 
        using h by simp 
      with `i<k` have "\<exists> C p q. p < q \<and> arrival (t C\<bullet>p) \<ge> arrival (t C\<bullet>q)" 
        by auto
      thus False
        using mi by (metis not_less)  
    qed
  next
    assume "arrival (t A\<bullet>i) \<le> date (t B\<bullet>j)"
    with assms show "A\<bullet>i \<rightarrow>t B\<bullet>j"
      by (metis hb_arrival tranclp.r_into_trancl)
  qed




section "Unitary Discretization"

text {*
  In this section we define the notion of unitary discretization and prove 
  the central lemma, namely the existence of a unitary discretization
  is equivalent to a simple condition involving three events.
*}

subsection "Discretization function"

definition discretization :: "(event \<Rightarrow> nat) \<Rightarrow> (event \<Rightarrow> tevent) \<Rightarrow> bool"
  where "discretization f t = (\<forall> x y. (x \<rightarrow>t y) \<longleftrightarrow>  f x < f y)"
 
function discr :: "trace \<Rightarrow> event \<Rightarrow> nat"
  where "discr t y = (Max (insert 0 (Suc ` discr t ` {x. x \<rightarrow>t y \<and> quasiperiodic t})))"
    by auto

termination
  proof (relation "measure (\<lambda>(t, y). card {x. x \<rightarrow>t y \<and> quasiperiodic t})")
    fix t y x
    assume "x \<in> {x. x \<rightarrow>t y \<and> quasiperiodic t}"
    hence "quasiperiodic t"
    and "x \<rightarrow>t y"
      by auto
    from hb_finite [OF this(1)] hb_decr [OF this]
    have "card {z. z \<rightarrow>t x} < card {x. x \<rightarrow>t y}"
      by (rule psubset_card_mono)
    thus "((t, x), (t, y)) \<in> measure (\<lambda>(t, y). card {x. x \<rightarrow>t y \<and> quasiperiodic t})"
      using `quasiperiodic t` by simp
  qed simp
declare discr.simps [simp del]

lemma qp_discr:
  assumes "quasiperiodic t"
  shows "discr t y = (Max (insert 0 (Suc ` discr t ` {x. x \<rightarrow>t y})))"
  using assms by (simp add: discr.simps)

lemma case_discr [simp]:
  assumes qp: "quasiperiodic t"
  shows "discr t y = (if {x. x \<rightarrow>t y} = {} then 0 
                      else Max ({discr t x | x. x \<rightarrow>t y}) + 1)"
  proof (cases "{x. x \<rightarrow>t y} = {}")
    assume "{x. x \<rightarrow>t y} = {}"
    moreover then have "discr t y = 0" 
      using qp_discr [OF qp] by simp
    ultimately show ?thesis
      by simp
  next
    assume notempty: "{x. x \<rightarrow>t y} \<noteq> {}"
    from hb_finite [OF qp] have "finite (discr t ` {x. x \<rightarrow>t y})" 
      by simp
    moreover have "discr t ` {x. x \<rightarrow>t y} = {discr t x|x. x \<rightarrow>t y}"
      by auto
    ultimately have "finite {discr t x |x. x \<rightarrow>t y}" 
      by simp
    from qp have "discr t y = (Max (insert 0 (Suc ` discr t ` {x. x \<rightarrow>t y})))"
      by (rule qp_discr)
    also from `finite {discr t x |x. x \<rightarrow>t y}` notempty
    have "... = Max (Suc ` {discr t x |x. x \<rightarrow>t y})"
      by (auto simp add: image_Collect)
    also from mono_Suc `finite {discr t x |x. x \<rightarrow>t y}` notempty
    have "... = Suc (Max {discr t x |x. x \<rightarrow>t y})"
      by (subst mono_Max_commute [where f=Suc]) simp_all
    finally show ?thesis
      using notempty by simp
  qed

subsection "Centra lemma UC is equivalent to UD"

subsubsection "UD implies UC"

lemma UD_concur:
  assumes UD:"discretization f t" 
  and "x \<parallel>t y"
  shows "f x = f y"
  proof (rule ccontr)
    assume "\<not> f x = f y"
    hence "x \<rightarrow>t y \<or> y \<rightarrow>t x"
    proof (cases "f x < f y")
      assume "f x < f y"
      with UD show ?thesis 
        using discretization_def by simp
    next 
      assume "\<not> f x < f y"
      with `\<not> f x = f y` have "f x > f y"
        by simp
      with UD show ?thesis 
        using discretization_def by simp
    qed
    with `x \<parallel>t y` show False 
      using concur_def by simp
  qed

lemma UDUC:
  assumes UD:"discretization f t"
  shows UC:"\<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
  proof
   assume "(\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
   then obtain x y z 
   where "x \<rightarrow>t y"
   and "x \<parallel>t z"
   and "y \<parallel>t z" 
     by auto
   with UD have "f x < f y" 
     using discretization_def by simp
   moreover from `x \<parallel>t z` have "f x = f z" 
     using assms by (simp add: UD_concur)
   moreover from `y \<parallel>t z` have "f y = f z" 
     using assms by (simp add: UD_concur)
   ultimately show False 
     by simp
  qed

subsubsection "UC implies UD"

lemma UCUD:
  assumes qp: "quasiperiodic t"
  and UC:"\<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
  shows UD:"\<exists> f. discretization f t" 
  proof -
    def f == "\<lambda> x. discr t x"

    { fix x y
      assume "x \<rightarrow>t y"
      have "f x < f y"
      proof (rule ccontr)
        assume "\<not> f x < f y"
        with qp have "finite {x. x\<rightarrow>t y}" 
           by (simp add: hb_finite)
        hence "finite {f x | x. x \<rightarrow>t y}" 
          by simp
        from `x \<rightarrow>t y` have "f x \<in> {f x | x. x \<rightarrow>t y}" 
          by auto
        with `finite {f x | x. x \<rightarrow>t y}` have "f x \<le> Max {f x::nat| x. x \<rightarrow>t y}" 
          by simp
        hence "f x < Max {f x::nat| x. x \<rightarrow>t y} + 1" 
          by auto
        from `x \<rightarrow>t y` have "{x. x \<rightarrow>t y} \<noteq> {}" 
          by auto
        with qp f_def have "f y = Max {f x| x. x \<rightarrow>t y} + 1" 
          by simp
        with `f x < Max {f x| x. x \<rightarrow>t y} + 1` have  "f x < f y" 
          by simp
        with `\<not> f x < f y` show False 
          by auto 
      qed 
    }
  
    moreover
    { fix x y
      assume "f y < f x"
      have f_hb1:"\<not> (x \<rightarrow>t y)"
      proof 
        assume "(x \<rightarrow>t y)"
        hence "x \<rightarrow>t y"
          by auto
        hence "f x < f y" 
          by (rule `\<And>ya xa. xa \<rightarrow>t ya \<Longrightarrow> f xa < f ya`)
        with `f y < f x` show False 
          by simp
      qed
    }
   
    moreover
    { fix x y z
      assume "f y = f z + 1"
      and "f x < f y"
      have "\<not> z \<rightarrow>t x"
      proof 
        assume "z \<rightarrow>t x"
        hence "f z < f x" 
          by (rule `\<And>ya xa. xa \<rightarrow>t ya \<Longrightarrow> f xa < f ya`)
        moreover from `f y = f z + 1` `f x < f y` have "f x \<le> f z" 
          by simp
        ultimately have "f z \<ge> f x" 
          by simp
        thus False 
          using `f z < f x` by simp
      qed
    } 
  
    moreover
    { fix y
      assume "f y > 0"
      have "\<exists> z. z \<rightarrow>t y \<and> f y = f z + 1"
       proof -
        have "{x. x \<rightarrow>t y} \<noteq> {}"
        proof 
          assume "{x. x \<rightarrow>t y} = {}"
           hence "{x. x \<rightarrow>t y} = {}"
            by simp
          with qp f_def have "f y = 0"  
            by simp
          thus False
            using `f y > 0` by simp
        qed 
        moreover with qp f_def have "f y =  Max {f x| x. x \<rightarrow>t y} + 1" 
          by simp
        moreover from qp have "finite {x. x\<rightarrow>t y}" 
          by (simp add: hb_finite)
        ultimately have "\<exists>x \<in> {x. x\<rightarrow>t y}. f x = Max {f x |x. x \<in> {x. x\<rightarrow>t y}}"
          by (metis (mono_tags) finite_max)       
        moreover have "{x. x \<in> {x. x\<rightarrow>t y}} = {x. x \<rightarrow>t y}" 
          by simp
        ultimately obtain z 
        where "z \<in> {x. x\<rightarrow>t y}"
        and "f z = Max{f x |x. x\<rightarrow>t y}" 
          by auto
        with `f y =  Max {f x| x. x \<rightarrow>t y} + 1` have "f y = f z + 1" 
          by simp
        from `z \<in> {x. x\<rightarrow>t y}` have "z \<rightarrow>t y" 
          by simp
        with `f y = f z + 1` show ?thesis 
          by auto
      qed
    }
   
    moreover
    { fix x y
      assume "f x < f y"
      have "x \<rightarrow>t y"
      proof (rule ccontr)
        assume "\<not> x \<rightarrow>t y" 
        from `f x < f y` have "\<not> y \<rightarrow>t x" 
          by (rule `\<And>ya xa. f ya < f xa \<Longrightarrow> \<not> xa \<rightarrow>t ya`)
        with `\<not> x \<rightarrow>t y` have "x \<parallel>t y" 
          using concur_def by simp
        from `f x < f y` have "f y > 0"
          by simp
        with f_def obtain z 
        where "z \<rightarrow>t y"
        and "f y = f z + 1"
          by (metis `\<And>ya. 0 < f ya \<Longrightarrow> \<exists>z.  z \<rightarrow>t ya \<and> f ya = f z + 1`)
        from `\<not> x \<rightarrow>t y` `z \<rightarrow>t y` have "\<not> x \<rightarrow>t z"
          by (metis tranclp_trans)
        moreover from `f y = f z + 1` `f x < f y` have "\<not> z \<rightarrow>t x"
          by (rule `\<And>z ya xa. \<lbrakk>f ya = f z + 1; f xa < f ya\<rbrakk> \<Longrightarrow> \<not> z \<rightarrow>t xa`)
        ultimately have "z \<parallel>t x" 
          using concur_def by simp
        from  `z \<rightarrow>t y` `x \<parallel>t y` `z \<parallel>t x` UC show False 
          using concur_def by auto
      qed 
    }
   
    ultimately show ?thesis 
      using discretization_def by metis
  qed

theorem concur_discretization:
   assumes qp:"quasiperiodic t"
   shows "(\<exists>f. discretization f t) \<longleftrightarrow> 
          (\<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z)))"
   proof 
       assume "\<exists>f. discretization f t"
       thus "\<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))" 
         by (metis UDUC)
   next
      assume "\<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
      with qp show "\<exists>f. discretization f t" 
        by (rule UCUD)
   qed

subsection "Discretizing two nodes systems"

text {*
  In this section we give the weakest condition to ensure that a systems of 
  two quasi-periodic nodes is unitary discretizable.
*}

subsubsection "Soundness"
    
lemma discretization_2_sound:
  assumes qp:"quasiperiodic t"
  and "card nodes = 2"
  and "T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
  shows "\<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
  proof
    assume "(\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
    then obtain x y z 
    where "x \<rightarrow>t y"
    and "x \<parallel>t z"
    and "y \<parallel>t z"
      by auto
    with qp have "node x \<noteq> node z" and "node y \<noteq> node z"
      by (simp_all add: hb_concur_nodes)
    with `card nodes = 2` have "node x = node y"
      by (metis card2_xyz node_coherent)
    from `node x = node y` `node x \<noteq> node z` obtain A B i j k
    where "A \<noteq> B"
    and "x = A\<bullet>i"
    and "y = A\<bullet>j"
    and "z = B\<bullet>k"
      by (metis (full_types) event.surjective unit.exhaust)
    with `x \<parallel>t z` `y \<parallel>t z` have h:"(A\<bullet>i \<parallel>t B\<bullet>k) \<and> (A\<bullet>j \<parallel>t B\<bullet>k)"
      by simp
    from `x \<rightarrow>t y` `x = A\<bullet>i` `y = A\<bullet>j` have "A\<bullet>i \<rightarrow>t A\<bullet>j" 
      by simp
    with `A\<bullet>i \<rightarrow>t A\<bullet>j` qp have "i < j" 
      by (simp add: hb_A_ij)    
    from qp obtain transmin: "\<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans (t A\<bullet>j)"
    and transmax_A: "trans (t A\<bullet>i) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
    and transmax_B: "trans (t B\<bullet>k) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
      using quasiperiodic_def by simp
    from qp `i < j` have "date (t A\<bullet>i) + T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>j)"
      by (rule qp_cone_lower_tmin)
    moreover from h have "\<not> (A\<bullet>i \<rightarrow>t B\<bullet>k)" 
      using concur_def by simp
    hence "date (t B\<bullet>k) < arrival (t A\<bullet>i)" 
      using qp `A \<noteq> B` by (metis event.select_convs(1) not_hb_realtime)
    hence "date (t B\<bullet>k) < date(t A\<bullet>i) + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using transmax_A by simp
    moreover from h have "\<not> (B\<bullet>k \<rightarrow>t A\<bullet>j)" 
      using concur_def by simp
    hence " date (t A\<bullet>j) < arrival (t B\<bullet>k)" 
      using qp `A \<noteq> B` by (metis event.select_convs(1) not_hb_realtime)
    hence "date (t A\<bullet>j) < date (t B\<bullet>k) + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using transmax_B by simp
    ultimately have "date (t A\<bullet>i) + T\<^sub>m\<^sub>i\<^sub>n < date (t A\<bullet>i) + \<tau>\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      by simp
    moreover have "\<tau>\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x = 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
      by (simp add: numerals)
    ultimately have "date (t A\<bullet>i) + T\<^sub>m\<^sub>i\<^sub>n < date (t A\<bullet>i) + 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      by simp
    thus False 
      using `2 * \<tau>\<^sub>m\<^sub>a\<^sub>x \<le> T\<^sub>m\<^sub>i\<^sub>n` by simp
  qed

subsubsection "Weakest condition"

lemma discretization_2_eg:
  assumes "card nodes = 2"
  and "T\<^sub>m\<^sub>i\<^sub>n < 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
  shows "\<exists>t. (quasiperiodic t)  \<and>  (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
  proof -
    from `card nodes = 2` finnode obtain A 
    where "A \<in> nodes"
      using node_coherent by auto
    with `card nodes = 2` finnode have "card (nodes - {A}) = 1" 
      by simp
    then obtain B 
    where "B \<in> nodes - {A}" 
      by (metis card_empty equals0I zero_neq_one)
    from `A \<in> nodes` `B \<in> nodes - {A}` have abnodes: "A \<in> nodes" "B \<in> nodes" "A \<noteq> B"  
      by auto
    from `T\<^sub>m\<^sub>i\<^sub>n < 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x` obtain \<epsilon>
    where "\<epsilon>/2 > 0"
    and "\<epsilon> = 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x - T\<^sub>m\<^sub>i\<^sub>n" 
      by simp     
    hence "\<tau>\<^sub>m\<^sub>a\<^sub>x - \<epsilon>/2 = T\<^sub>m\<^sub>i\<^sub>n/2" 
      by linarith
    moreover with Tminpos have "\<tau>\<^sub>m\<^sub>a\<^sub>x - \<epsilon>/2 > 0" 
      by simp
    ultimately have "\<tau>\<^sub>m\<^sub>a\<^sub>x - \<epsilon>/2 < \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using taumaxpos `0 < \<epsilon> / 2` by simp

    def eg == "\<lambda>e :: event.
               if node e = A then \<lparr> date = act e * T\<^sub>m\<^sub>i\<^sub>n, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>
          else if node e = B then \<lparr> date = \<tau>\<^sub>m\<^sub>a\<^sub>x- \<epsilon>/2 + act e * T\<^sub>m\<^sub>i\<^sub>n, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>
          else \<lparr> date = act e * T\<^sub>m\<^sub>i\<^sub>n, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>"
    
    have "\<forall> e. trans (eg e) = \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using eg_def by simp
    hence "\<forall> e. \<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans (eg e) \<and> trans (eg e) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using eg_def taubounds by simp 
    moreover have "\<forall> e. date (eg (step e)) - date (eg e) = T\<^sub>m\<^sub>i\<^sub>n"
      using eg_def by simp
    hence "\<forall> e. T\<^sub>m\<^sub>i\<^sub>n \<le> date (eg (step e)) - date (eg e) 
             \<and> date (eg (step e)) - date (eg e) \<le> T\<^sub>m\<^sub>a\<^sub>x"
      using Tbounds by simp
    moreover have "\<forall> e. 0 \<le> date(eg e)" 
      using eg_def Tminpos `\<tau>\<^sub>m\<^sub>a\<^sub>x - \<epsilon>/2 > 0` by simp      
    ultimately have qp:"quasiperiodic eg" 
      using quasiperiodic_def by simp
   
    have mi:"\<forall> N p q. p < q \<longrightarrow> arrival (eg N\<bullet>p) < arrival (eg N\<bullet>q)"
     using eg_def Tminpos by (simp add: `\<forall>e. tevent.trans (eg e) = \<tau>\<^sub>m\<^sub>a\<^sub>x`)
    
    have a0:"eg A\<bullet>0 = \<lparr> date = 0, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>"
    and b0:"eg B\<bullet>0 = \<lparr> date = \<tau>\<^sub>m\<^sub>a\<^sub>x - \<epsilon>/2, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>"
    and a1:"eg A\<bullet>1 = \<lparr> date = T\<^sub>m\<^sub>i\<^sub>n, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>"
      using abnodes eg_def by simp_all

    have "A\<bullet>0 \<rightarrow>eg A\<bullet>1 \<and> A\<bullet>0 \<parallel>eg B\<bullet>0 \<and> B\<bullet>0 \<parallel>eg A\<bullet>1"
    proof -
      have "A\<bullet>0 \<rightarrow>eg A\<bullet>1"
        by (simp add: hb_subsequent tranclp.r_into_trancl)

      moreover
      { from a0 b0 `\<tau>\<^sub>m\<^sub>a\<^sub>x - \<epsilon>/2 < \<tau>\<^sub>m\<^sub>a\<^sub>x` have "date (eg B\<bullet>0) < arrival (eg A\<bullet>0)" 
          by simp
        with qp mi `A \<noteq> B` have "\<not> A\<bullet>0 \<rightarrow>eg B\<bullet>0" 
          by (metis hb_realtime not_le) 
        moreover from `\<tau>\<^sub>m\<^sub>a\<^sub>x - \<epsilon>/2 > 0` taumaxpos this a0 b0 
        have "date (eg A\<bullet>0) < arrival (eg B\<bullet>0)"
          by simp 
        hence "\<not> B\<bullet>0 \<rightarrow>eg A\<bullet>0" 
          using `A \<noteq> B` mi qp by (metis hb_realtime not_le)
        ultimately have "A\<bullet>0 \<parallel>eg B\<bullet>0" 
          using concur_def by simp
      }
       
      moreover
      { from b0 a1 Tmaxpos `\<tau>\<^sub>m\<^sub>a\<^sub>x - \<epsilon>/2 = T\<^sub>m\<^sub>i\<^sub>n/2` Tminpos have "date (eg B\<bullet>0) < date (eg A\<bullet>1)" 
         by simp
        moreover with a1 taumaxpos have "arrival(eg A\<bullet>1) > date(eg A\<bullet>1)"
          by auto
        ultimately have "date (eg B\<bullet>0) < arrival (eg A\<bullet>1)" 
          by simp
        hence "\<not> A\<bullet>1 \<rightarrow>eg B\<bullet>0" 
          using `A \<noteq> B` mi qp by (metis hb_realtime not_le) 
        moreover from b0 `\<tau>\<^sub>m\<^sub>a\<^sub>x - \<epsilon> / 2 = T\<^sub>m\<^sub>i\<^sub>n / 2` have "arrival (eg B\<bullet>0) = \<tau>\<^sub>m\<^sub>a\<^sub>x + T\<^sub>m\<^sub>i\<^sub>n/2" 
          by simp
        hence "date (eg A\<bullet>1) < arrival (eg B\<bullet>0)"
          using  a1 `\<tau>\<^sub>m\<^sub>a\<^sub>x - \<epsilon> / 2 < \<tau>\<^sub>m\<^sub>a\<^sub>x` `\<tau>\<^sub>m\<^sub>a\<^sub>x - \<epsilon> / 2 = T\<^sub>m\<^sub>i\<^sub>n / 2` by simp
        hence "\<not> B\<bullet>0 \<rightarrow>eg A\<bullet>1" 
          using `A \<noteq> B` mi qp by (metis hb_realtime not_le)
        ultimately have b0a1:"B\<bullet>0 \<parallel>eg A\<bullet>1"
          using concur_def by simp
        }
     
      ultimately show ?thesis 
        by simp
    qed
    with qp show ?thesis 
      using concur_def by auto
  qed

lemma discretization_2_weakest:
  assumes "card nodes = 2"
  and "\<forall>t. (quasiperiodic t)  \<longrightarrow>  \<not>(\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
  shows "T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
  proof (rule ccontr)
    assume "\<not> T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
    hence "T\<^sub>m\<^sub>i\<^sub>n < 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
      by simp
    with `card nodes = 2` 
    have "\<exists>t. (quasiperiodic t)  \<and>  (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))" 
      by (rule discretization_2_eg)
    thus False 
      using assms(2) by auto
  qed

theorem discretization_2:
  assumes "card nodes = 2"
  and "quasiperiodic t"
  shows "(\<forall>t. quasiperiodic t  \<longrightarrow> (\<exists>f. discretization f t)) \<longleftrightarrow> (T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x)"
  proof -
    have "\<forall>t. quasiperiodic t \<longrightarrow> 
         (\<exists>f. discretization f t) \<longleftrightarrow> \<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
    by (simp add: concur_discretization)    
    moreover have "(\<forall>t. quasiperiodic t \<longrightarrow> \<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))) 
                    \<longleftrightarrow> (T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x)"
    proof
      assume "\<forall>t. quasiperiodic t \<longrightarrow> \<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
      with `card nodes = 2` show "T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
        by (rule discretization_2_weakest)
    next
      assume "T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
      show "\<forall>t. quasiperiodic t \<longrightarrow> \<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
      proof
        fix t
        show "quasiperiodic t \<longrightarrow> \<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
        proof
          assume qp:"quasiperiodic t"
          thus "\<not> (\<exists> x y z. (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))" 
            using `T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x` `card nodes = 2` by (metis discretization_2_sound)
        qed
      qed
    qed
    ultimately show ?thesis 
      by simp
  qed

subsection "Discretizing general systems"

text {*
  We prove here that general quasi-periodic systems of more than two nodes are 
  not unitary discretizable.
*}

lemma discretization_eg:
  assumes "2 < card nodes"
  shows "\<exists>t x y z. quasiperiodic t \<and> x \<rightarrow>t y \<and> x \<parallel>t z \<and> y \<parallel>t z"
  proof -
    from assms(1) finnode obtain A 
    where "A \<in> nodes"
      by (metis all_not_in_conv card_eq_0_iff less_nat_zero_code)
    moreover with assms finnode obtain B 
    where "B \<in> nodes - {A}"
      by (metis Suc_1 Suc_leI card_0_eq card_Suc_Diff1 finite.cases 
          finite_Diff insertI1 less_le_trans not_less_iff_gr_or_eq zero_less_Suc)
    ultimately obtain C 
    where "C \<in> nodes - {A, B}"
      using assms finnode by (metis Diff_insert2 One_nat_def Suc_1 Suc_leI 
      all_not_in_conv card.insert_remove card_empty finite.emptyI insert_Diff_single 
      insert_absorb lessI not_le)
    from `A \<in> nodes` `B \<in> nodes - {A}` `C \<in> nodes - {A, B}`
    have abcnodes: "A \<in> nodes" "B \<in> nodes" "C \<in> nodes" "A \<noteq> B" "B \<noteq> C" "C \<noteq> A" 
      by auto

    def eg == "\<lambda>e :: event.
                 if node e = A then \<lparr> date = act e * T\<^sub>m\<^sub>a\<^sub>x, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>
            else if node e = B then \<lparr> date = \<tau>\<^sub>m\<^sub>a\<^sub>x + act e * T\<^sub>m\<^sub>a\<^sub>x, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>
            else if node e = C then \<lparr> date = \<tau>\<^sub>m\<^sub>a\<^sub>x / 2 + act e * T\<^sub>m\<^sub>a\<^sub>x, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>
            else \<lparr> date = act e * T\<^sub>m\<^sub>a\<^sub>x, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>"

    have "\<forall> e. trans (eg e) = \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using eg_def by simp
    hence "\<forall> e. \<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans (eg e) \<and> trans (eg e) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using eg_def taubounds by simp 
    moreover have "\<forall> e. date (eg (step e)) - date (eg e) = T\<^sub>m\<^sub>a\<^sub>x"
      using eg_def by simp
    hence "\<forall> e. T\<^sub>m\<^sub>i\<^sub>n \<le> date (eg (step e)) - date (eg e) 
             \<and> date (eg (step e)) - date (eg e) \<le> T\<^sub>m\<^sub>a\<^sub>x"
      using Tbounds by simp
    moreover have "\<forall> e. 0 \<le> date(eg e)" 
      using eg_def Tmaxpos taumaxpos' by simp     
    ultimately have qp:"quasiperiodic eg" 
      using quasiperiodic_def by simp

    have mi:"\<forall> N p q. p < q \<longrightarrow> arrival (eg N\<bullet>p) < arrival (eg N\<bullet>q)"
     using eg_def Tmaxpos by (simp add: `\<forall>e. tevent.trans (eg e) = \<tau>\<^sub>m\<^sub>a\<^sub>x`)

    from abcnodes
    have a0:"eg A\<bullet>0 = \<lparr> date = 0, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>"
    and b0:"eg B\<bullet>0 = \<lparr> date = \<tau>\<^sub>m\<^sub>a\<^sub>x, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>"
    and c0:"eg C\<bullet>0 = \<lparr> date = \<tau>\<^sub>m\<^sub>a\<^sub>x / 2, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>"
      using eg_def by simp_all
     
    have "A\<bullet>0 \<rightarrow>eg B\<bullet>0 \<and> A\<bullet>0 \<parallel>eg C\<bullet>0 \<and> B\<bullet>0 \<parallel>eg C\<bullet>0"
    proof -
      { from a0 b0 have "arrival (eg A\<bullet>0) \<le> date (eg B\<bullet>0)" 
          by simp
        hence "A\<bullet>0 \<rightarrow>eg B\<bullet>0" 
          using qp a0 b0 `A \<noteq> B` not_hb_realtime by fastforce
      }
   
      moreover
      { from taumaxpos have "\<tau>\<^sub>m\<^sub>a\<^sub>x/2 < \<tau>\<^sub>m\<^sub>a\<^sub>x" 
          by simp
        from this a0 c0 tauminpos have "date (eg C\<bullet>0) < arrival (eg A\<bullet>0)"
          by simp
        with qp mi `C \<noteq> A` have "\<not> A\<bullet>0 \<rightarrow>eg C\<bullet>0" 
          by (metis hb_realtime not_le)
        moreover from taumaxpos have "0 < \<tau>\<^sub>m\<^sub>a\<^sub>x/2 + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
          by simp
        from this a0 c0 have "date (eg A\<bullet>0) < arrival (eg C\<bullet>0)" 
          by simp 
        hence "\<not> C\<bullet>0 \<rightarrow>eg A\<bullet>0" 
          using `C \<noteq> A` mi qp by (metis hb_realtime not_le)
        ultimately have "A\<bullet>0 \<parallel>eg C\<bullet>0" 
          using concur_def by simp
      }

      moreover
      { from taumaxpos have "\<tau>\<^sub>m\<^sub>a\<^sub>x/2 < \<tau>\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
          by simp
        from this b0 c0 tauminpos have "date (eg C\<bullet>0) < arrival (eg B\<bullet>0)" 
          by simp
        hence "\<not> B\<bullet>0 \<rightarrow>eg C\<bullet>0" 
          using `B \<noteq> C` mi qp by (metis hb_realtime not_le)
        moreover from taumaxpos have "\<tau>\<^sub>m\<^sub>a\<^sub>x < \<tau>\<^sub>m\<^sub>a\<^sub>x/2 + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
          by simp
        with b0 c0 have "date (eg B\<bullet>0) < arrival (eg C\<bullet>0)" 
          by simp 
        hence "\<not> C\<bullet>0 \<rightarrow>eg B\<bullet>0" 
          using `B \<noteq> C` mi qp by (metis hb_realtime not_le)
        ultimately have "B\<bullet>0 \<parallel>eg C\<bullet>0"
          using concur_def by simp
      }      
      
      ultimately show ?thesis 
        by simp
    qed
    with qp show ?thesis 
      by auto
  qed

theorem discretization:
  assumes "2 < card nodes"
  shows "\<exists>t. quasiperiodic t \<and>  \<not> (\<exists>f. discretization f t)"
  proof -
    have "(\<exists>t. quasiperiodic t \<and> \<not> (\<exists>f. discretization f t)) 
           \<longleftrightarrow> (\<exists>t x y z. quasiperiodic t \<and> (x \<rightarrow>t y) \<and> (x \<parallel>t z) \<and> (y \<parallel>t z))"
    by (metis concur_discretization)
    with `2 < card nodes` show ?thesis 
      by (metis discretization_eg)
  qed

section "Quasi-synchronous Abstraction"

text {*
  In this section we link the quasi-synchronous abstraction of Caspi with 
  quasi-periodic system of two nodes.
*}

subsection "Soundness"

lemma not_quasi_synchrony_sound_case1:
  assumes qp:"quasiperiodic t"
  and "A \<noteq> B"
  and "T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
  and "n > 0"
  and "(\<not> A\<bullet>i \<rightarrow>t B\<bullet>j)" 
  and "(A\<bullet>(i+n) \<rightarrow>t B\<bullet>(j+1))"
  shows "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n < T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"
  proof -
    from `T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x`  taumaxpos' tauminpos have "T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n > \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      by simp
    with qp have mi:"\<forall> C p q. p < q \<longrightarrow> arrival (t C\<bullet>p) < arrival (t C\<bullet>q)"
      by (rule message_inversion) 
    from qp obtain transmin: "\<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans (t A\<bullet>(i+n))"
    and transmax: "trans (t A\<bullet>i) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
      using quasiperiodic_def by auto
    from qp `A \<noteq> B` `\<not> A\<bullet>i \<rightarrow>t B\<bullet>j` have "arrival (t A\<bullet>i) > date (t B\<bullet>j)"
      by (metis event.select_convs(1) not_hb_realtime) 
    hence "date (t B\<bullet>j) < date (t A\<bullet>i) + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using transmax by simp
    moreover from qp `A \<noteq> B` mi `A\<bullet>(i+n) \<rightarrow>t B\<bullet>(j+1)` 
    have "date (t B\<bullet>(j+1)) \<ge> arrival (t A\<bullet>(i+n))" 
      by (metis hb_realtime)
    hence "date (t B\<bullet>(j+1)) \<ge> date (t A\<bullet>(i+n)) + \<tau>\<^sub>m\<^sub>i\<^sub>n" 
      using transmin by simp
    moreover from qp have "date (t B\<bullet>(j+1)) - date (t B\<bullet>j) \<le> T\<^sub>m\<^sub>a\<^sub>x" 
      by (metis Suc_eq_plus1 qp_suc)
    hence "date (t B\<bullet>(j+1)) \<le> date (t B\<bullet>j) + T\<^sub>m\<^sub>a\<^sub>x" 
      by simp
    moreover have "n * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>(i+n)) - date (t A\<bullet>i)"  
      using qp `n > 0` by (simp add: qp_cone_lower)
    ultimately show "n *T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n < T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"  
      by simp
  qed


lemma not_quasi_synchrony_sound_case2:
  assumes qp:"quasiperiodic t"
  and "A \<noteq> B"
  and "T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
  and "n > 0"
  and "(\<not> A\<bullet>i \<rightarrow>t B\<bullet>j)"
  and "(\<not> B\<bullet>(j+1) \<rightarrow>t A\<bullet>(i+n))"
  shows "n * T\<^sub>m\<^sub>i\<^sub>n < T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x"
  proof -
    from `T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x`  tauminpos taumaxpos' have mi:"T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n > \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      by simp
    from qp obtain transmaxb: "trans (t B\<bullet>(j+1)) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
    and transmaxa: "trans (t A\<bullet>i) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
      using quasiperiodic_def by auto
    from qp `A \<noteq> B` `\<not> A\<bullet>i \<rightarrow>t B\<bullet>j` have "arrival (t A\<bullet>i) > date (t B\<bullet>j)"
      by (metis event.select_convs(1) not_hb_realtime) 
    hence "date (t B\<bullet>j) < date (t A\<bullet>i) + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using transmaxa by simp
    moreover from qp `A \<noteq> B` `\<not> B\<bullet>(j+1) \<rightarrow>t A\<bullet>(i+n)` 
    have "date (t A\<bullet>(i+n)) < arrival (t B\<bullet>(j+1))" 
      by (metis event.select_convs(1) not_hb_realtime) 
    hence "date (t A\<bullet>(i+n)) < date (t B\<bullet>(j+1)) + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using transmaxb by simp
    moreover from qp have "date (t B\<bullet>(j+1)) - date (t B\<bullet>j) \<le> T\<^sub>m\<^sub>a\<^sub>x" 
      by (metis Suc_eq_plus1 qp_suc)
    hence "date (t B\<bullet>(j+1)) \<le> date (t B\<bullet>j) + T\<^sub>m\<^sub>a\<^sub>x" 
      by simp
    moreover have "n * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>(i+n)) - date (t A\<bullet>i)"  
      using qp `n > 0` by (simp add: qp_cone_lower)
    ultimately show "n * T\<^sub>m\<^sub>i\<^sub>n < T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x" 
      by simp
  qed

  
lemma quasi_synchrony_sound:
  assumes "discretization f t"
  and qp:"quasiperiodic t"
  and "A \<noteq> B"
  and "T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
  and "n > 0"
  and "n * T\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
  shows "\<not> (f B\<bullet>j \<le> f A\<bullet>i \<and> f A\<bullet>(i+n) \<le> f B\<bullet>(j+1))"
  proof 
    assume "(f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1))"
    hence "f B\<bullet>j \<le> f A\<bullet>i" 
    and "f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)" 
      by simp_all
    moreover from `n * T\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x` taumaxpos' tauminpos' 
    have "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      by simp
    ultimately show False
    proof (cases "f A\<bullet>(i+n) = f B\<bullet>(j+1)")
      assume "f A\<bullet>(i+n) = f B\<bullet>(j+1)"
      with assms(1) have "\<not> B\<bullet>(j+1) \<rightarrow>t A\<bullet>(i+n)" 
        using discretization_def by simp
      moreover from assms(1) `f B\<bullet>j \<le> f A\<bullet>i` have "\<not> A\<bullet>i \<rightarrow>t B\<bullet>j" 
        using discretization_def by simp
      ultimately have "n * T\<^sub>m\<^sub>i\<^sub>n < T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x" 
        using assms(2-5) by (simp add: not_quasi_synchrony_sound_case2)
      thus False 
        using `n * T\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x` by simp
    next 
      assume "\<not> f A\<bullet>(i+n) = f B\<bullet>(j+1)"
      with `f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)` have "f A\<bullet>(i+n) < f B\<bullet>(j+1)" 
        by simp
      with assms(1) have "A\<bullet>(i+n) \<rightarrow>t B\<bullet>(j+1)" 
        using discretization_def by simp
      moreover from assms(1) `f B\<bullet>j \<le> f A\<bullet>i` have "\<not> A\<bullet>i \<rightarrow>t B\<bullet>j" 
        using discretization_def by simp
      ultimately have "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n < T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
        using assms(2-5) by (simp add: not_quasi_synchrony_sound_case1)
      thus False 
        using `n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x` by simp
    qed
  qed

subsection "Weakest condition"

lemma quasi_synchrony_eg:
  assumes "A \<noteq> B"
  and "T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
  and "n > 0"
  and "\<not> (\<exists> t i j. quasiperiodic t
          \<and>  (\<not> A\<bullet>i \<rightarrow>t B\<bullet>j) \<and> (\<not> B\<bullet>(j+1) \<rightarrow>t A\<bullet>(i+n)))"
  shows "n * T\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x" 
  proof (rule ccontr)
    assume "\<not> n * T\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x"
    hence "\<exists> t i j.  quasiperiodic t  
           \<and>  (\<not> A\<bullet>i \<rightarrow>t B\<bullet>j) \<and> (\<not> B\<bullet>(j+1) \<rightarrow>t A\<bullet>(i+n))"
    proof -
      from `T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x`  tauminpos taumaxpos have mit:"T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n > \<tau>\<^sub>m\<^sub>a\<^sub>x" 
        by simp
      from `\<not> n * T\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x` obtain \<epsilon>
      where "\<epsilon>/2 > 0"
      and "\<epsilon> = T\<^sub>m\<^sub>a\<^sub>x + 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x - n * T\<^sub>m\<^sub>i\<^sub>n" 
        by simp
    
      def eg == "\<lambda>e :: event.
                 if node e = A \<and> act e = 0 then \<lparr> date = \<epsilon>/2, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>
            else if node e = B then \<lparr> date = \<tau>\<^sub>m\<^sub>a\<^sub>x + act e * T\<^sub>m\<^sub>a\<^sub>x, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>
            else \<lparr> date = \<epsilon>/2 + act e * T\<^sub>m\<^sub>i\<^sub>n, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>"

      have "\<forall> e. trans (eg e) = \<tau>\<^sub>m\<^sub>a\<^sub>x" 
        using eg_def by simp
      hence "\<forall> e. \<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans (eg e) \<and> trans (eg e) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x" 
        using eg_def taubounds by simp 
      moreover have "\<forall> e. date (eg (step e)) - date (eg e) = T\<^sub>m\<^sub>i\<^sub>n
              \<or> date (eg (step e)) - date (eg e) = T\<^sub>m\<^sub>a\<^sub>x "
        using eg_def `A \<noteq> B` by simp
      hence "\<forall> e. T\<^sub>m\<^sub>i\<^sub>n \<le> date (eg (step e)) - date (eg e) 
               \<and> date (eg (step e)) - date (eg e) \<le> T\<^sub>m\<^sub>a\<^sub>x"
        using Tbounds by auto
      moreover have "\<forall> e. 0 \<le> date(eg e)" 
        using eg_def Tmaxpos Tminpos taumaxpos' `\<epsilon>/2 > 0` by simp    
      ultimately have qp:"quasiperiodic eg" 
        using quasiperiodic_def by simp

      have a0:"arrival (eg A\<bullet>0) = \<tau>\<^sub>m\<^sub>a\<^sub>x + \<epsilon>/2"
      and b0:"date (eg B\<bullet>0) = \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      and b1:"arrival (eg B\<bullet>1) =  T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x "
      and an:"date (eg A\<bullet>n) = \<epsilon>/2 + n * T\<^sub>m\<^sub>i\<^sub>n" 
        using eg_def `A \<noteq> B` by simp_all

      from qp mit have mi:"\<forall> C p q. p < q \<longrightarrow> arrival (eg C\<bullet>p) < arrival (eg C\<bullet>q)"
        by (rule message_inversion)

      from `\<epsilon> = T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x - n * T\<^sub>m\<^sub>i\<^sub>n` `\<epsilon>/2 > 0` have "\<epsilon>/2 + n * T\<^sub>m\<^sub>i\<^sub>n < T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x" 
        by linarith    
      with an b1  have "date (eg A\<bullet>n) < arrival (eg B\<bullet>1)" 
        by simp
      with qp mi `A \<noteq> B` have "\<not> B\<bullet>1 \<rightarrow>eg A\<bullet>n" 
        by (metis hb_realtime not_le)
      moreover from a0 b0 `\<epsilon>/2 >0` taumaxpos have "date (eg B\<bullet>0) < arrival (eg A\<bullet>0)" 
        by auto
      with qp mi `A \<noteq> B` have "\<not> A\<bullet>0 \<rightarrow>eg B\<bullet>0"
        by (metis hb_realtime not_le)
      ultimately have "(\<not> A\<bullet>0 \<rightarrow>eg B\<bullet>0) \<and> (\<not> B\<bullet>1 \<rightarrow>eg A\<bullet>n)" 
        by simp
      thus ?thesis
        using qp by fastforce
    qed
    with assms(4) show False 
      by auto
  qed


lemma quasi_synchrony_weakest:
  assumes "card nodes = 2"
  and "A \<noteq> B"
  and "T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
  and "n > 0"
  and "\<not> (\<exists> t i j f. 
          quasiperiodic t \<and> 
          discretization f t \<and>
          (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)))"
  shows "n * T\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x" 
  proof (rule ccontr)
    assume "\<not> n * T\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x"
    with assms(2-4) 
    have "\<exists> t i j f. 
            quasiperiodic t \<and>  
            (\<not> A\<bullet>i \<rightarrow>t B\<bullet>j) \<and> (\<not> B\<bullet>(j+1) \<rightarrow>t A\<bullet>(i+n))"
      by (metis quasi_synchrony_eg)
    then obtain t i j 
    where qp:"quasiperiodic t"
    and "(\<not> A\<bullet>i \<rightarrow>t B\<bullet>j)"
    and "(\<not> B\<bullet>(j+1) \<rightarrow>t A\<bullet>(i+n))" 
      by auto    
    moreover from assms(1) assms(3) qp obtain f 
    where f_discr:"discretization f t" 
      by (metis discretization_2)
    moreover have "(f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1))"
    proof -
      from f_discr `(\<not> A\<bullet>i \<rightarrow>t B\<bullet>j)` have "f B\<bullet>j \<le> f A\<bullet>i" 
        using discretization_def by simp
      moreover from f_discr `(\<not> B\<bullet>(j+1) \<rightarrow>t A\<bullet>(i+n))` 
      have "f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)" 
        using  discretization_def by simp
      ultimately show "(f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1))" 
        by simp
    qed
    ultimately have "\<exists> t i j f. quasiperiodic t 
                  \<and> discretization f t
                  \<and> (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1) )"
      by auto
    thus False 
      using assms(5) by simp
  qed


theorem quasi_synchrony:
  assumes "card nodes = 2"
  and "A \<noteq> B"
  and "T\<^sub>m\<^sub>i\<^sub>n \<ge> 2 * \<tau>\<^sub>m\<^sub>a\<^sub>x"
  and "n > 0"
  shows "\<not> (\<exists> t i j f. 
            quasiperiodic t  \<and>
            discretization f t \<and>
            (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)))
       \<longleftrightarrow> n * T\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x"
  proof
    assume "\<not> (\<exists> t i j f. 
               quasiperiodic t \<and> 
               discretization f t \<and> 
               (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)))"
    with assms show "n * T\<^sub>m\<^sub>i\<^sub>n  \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x"
      by (rule quasi_synchrony_weakest)
  next
    assume "n * T\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x"
    show "\<not> (\<exists> t i j f. 
             quasiperiodic t \<and> 
             discretization f t \<and>
             (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)))" 
    proof
      assume "(\<exists> t i j f. 
             quasiperiodic t \<and> 
             discretization f t \<and>
             (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i + n) \<le> f B\<bullet>(j + 1)))"
      then obtain t i j f
      where qp:"quasiperiodic t"
      and "discretization f t"
      and "(f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i + n) \<le> f B\<bullet>(j + 1))" 
        by auto
      from `discretization f t` qp assms(2-4) `n * T\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + 2*\<tau>\<^sub>m\<^sub>a\<^sub>x` 
      have "\<not> (f B\<bullet>j \<le> f A\<bullet>i \<and> f A\<bullet>(i+n) \<le> f B\<bullet>(j+1))" 
        by (rule quasi_synchrony_sound)
      with `(f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i + n) \<le> f B\<bullet>(j + 1))` show False 
        by simp
    qed
  qed


section "Quasi-Synchrony on Relaxed Communication"

text {*
  In this section we link the quasi-synchronous abstraction with 
  quasi-periodic systems of, possibly, more than two nodes, assuming that there is 
  no forbidden topologies in the communication graph.
*}

subsection "Relaxed communication"

text {*
  We define here the notion of relaxed unitary discretization 
  that only constrains events occuring on communicating nodes.
*}

text {*
  Now the happened-before relation only involves events that occur on 
  communicating nodes.
*}

definition chb ("_ \<hookrightarrow>_ _" [100, 100] 100)
  where "x \<hookrightarrow>t y == com (node x) (node y) \<and> x \<rightarrow>t y"

definition relax_discr :: 
  "(event \<Rightarrow> nat) \<Rightarrow> (event \<Rightarrow> tevent) \<Rightarrow> bool"
  where "relax_discr f t = (\<forall> x y. f x < f y  \<longleftrightarrow> x \<hookrightarrow>t y)"

lemma f_relax_nhb:
  assumes "relax_discr f t" 
  and "com A B"
  and "f B\<bullet>j \<le> f A\<bullet>i"
  shows "\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j"
  proof
    assume "A\<bullet>i \<hookrightarrow>t B\<bullet>j"
    with `com A B` `relax_discr f t` have "f A\<bullet>i < f B\<bullet>j" 
      using relax_discr_def chb_def by auto
    thus False 
      using `f B\<bullet>j \<le> f A\<bullet>i` by simp
  qed
 
lemma nhb_f_reflax:
  assumes "relax_discr f t"
  and "com A B" 
  and "\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j"
  shows "f B\<bullet>j \<le> f A\<bullet>i"
  proof (rule ccontr)
    assume "\<not> f B\<bullet>j \<le> f A\<bullet>i"
    hence "f B\<bullet>j > f A\<bullet>i" 
      by simp
    with `com A B` assms(1) have "A\<bullet>i \<hookrightarrow>t B\<bullet>j" 
      using relax_discr_def chb_def by simp
    thus False 
      using `\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j` by simp
  qed


definition tight_discr :: 
  "(event \<Rightarrow> nat) \<Rightarrow> (event \<Rightarrow> tevent) \<Rightarrow> bool"
  where "tight_discr f t = 
          (relax_discr f t \<and>
          (\<forall> A B i j. 
             com A B \<and>
             f B\<bullet>j \<le> f A\<bullet>i \<and> f A\<bullet>i < f B\<bullet>(j+1) \<longrightarrow> f A\<bullet>i = f B\<bullet>j))"

text {*
  This is the most concise discretization. This property comes from
  the proof of the theorem on forbidden topologies (admitted here).
  If this discretization is not possible there exists an event @{text "C\<bullet>k"} such that
*}
text {*
  @{text "f B\<bullet>j < f C\<bullet>k \<le> f A\<bullet>i"}, that is, @{text "B\<bullet>j \<rightarrow>1 C\<bullet>k \<rightarrow>0 A\<bullet>i"}, or 
*}
text {*
  @{text "f B\<bullet>j \<le> f C\<bullet>k < f A\<bullet>i"}, that is, @{text "B\<bullet>j \<rightarrow>0 C\<bullet>k \<rightarrow>1 A\<bullet>i"}.
*}
text {*
  In both cases we get communication pattern @{text C\<^sub>0}.  In the following we assume 
  that assumptions of the theorem on forbidden topologies holds. Hence
  for all quasi-periodic trace, there exists a tight discretization. 
*}


lemma f_tight:
  assumes "tight_discr f t"
  and "com A B"
  and "A \<noteq> B"
  and "f B\<bullet>j \<le> f A\<bullet>i"
  and "f A\<bullet>i < f B\<bullet>(j+1)"
  shows "f A\<bullet>i= f B\<bullet>j"
  using assms using tight_discr_def relax_discr_def by simp

subsection "Soundness"

lemma not_qs_relax_sound_case1:
  assumes qp:"quasiperiodic t"
  and "\<forall> C p q. p < q \<longrightarrow> arrival (t C\<bullet>p) < arrival (t C\<bullet>q)"
  and "A \<noteq> B"
  and "com A B"
  and "n > 0"
  and "(\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j)"
  and "(A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+1))"
  shows "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n < T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"
  proof  -
    from qp obtain transmin: "\<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans (t A\<bullet>(i+n))"
    and transmax: "trans (t A\<bullet>i) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
      using quasiperiodic_def by auto
    from qp `A \<noteq> B` `com A B` `\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j` have "arrival (t A\<bullet>i) > date (t B\<bullet>j)" 
      using chb_def not_hb_realtime by simp
    hence "date (t B\<bullet>j) < date (t A\<bullet>i) + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using transmax by simp
    moreover from qp `A \<noteq> B` `com A B` assms(2) `A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+1)` 
    have "date (t B\<bullet>(j+1)) \<ge> arrival (t A\<bullet>(i+n))"
      using chb_def hb_realtime by simp
    hence "date (t B\<bullet>(j+1)) \<ge> date (t A\<bullet>(i+n)) + \<tau>\<^sub>m\<^sub>i\<^sub>n" 
      using transmin by simp
    moreover from qp have "date (t B\<bullet>(j+1)) - date (t B\<bullet>j) \<le> T\<^sub>m\<^sub>a\<^sub>x" 
      using Suc_eq_plus1 qp_suc by simp
    hence "date (t B\<bullet>(j+1)) \<le> date (t B\<bullet>j) + T\<^sub>m\<^sub>a\<^sub>x" 
      by simp
    moreover have "n * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>(i+n)) - date (t A\<bullet>i)"  
      using qp `n > 0` by (simp add: qp_cone_lower)
    ultimately show "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n < T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      by simp
  qed


lemma not_qs_relax_sound_case2:
  assumes qp:"quasiperiodic t"
  and "\<forall> t C p q. p < q \<longrightarrow> arrival (t C\<bullet>p) < arrival (t C\<bullet>q)"
  and "A \<noteq> B"
  and "com A B"
  and "n > 0"
  and "(\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j)"
  and "(A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+2))"
  shows "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n < 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"
  proof -
    from qp obtain transmin: "\<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans (t A\<bullet>(i+n))"
    and transmax: "trans (t A\<bullet>i) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x"
      using quasiperiodic_def by auto
    from qp `A \<noteq> B` `com A B` `\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j` have "arrival (t A\<bullet>i) > date (t B\<bullet>j)"
      using chb_def not_hb_realtime by simp
    hence "date (t B\<bullet>j) < date (t A\<bullet>i) + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      using transmax by simp
    moreover from qp `A \<noteq> B` `com A B` assms(2) `A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+2)` 
    have "date (t B\<bullet>(j+2)) \<ge> arrival (t A\<bullet>(i+n))" 
      using chb_def hb_realtime by simp
    hence "date (t B\<bullet>(j+2)) \<ge> date (t A\<bullet>(i+n)) + \<tau>\<^sub>m\<^sub>i\<^sub>n" 
      using transmin by simp
    moreover from qp have "date (t B\<bullet>(j+2)) - date (t B\<bullet>j) \<le> (j+2 - j)*T\<^sub>m\<^sub>a\<^sub>x"
      by (metis Suc_eq_plus1 add.assoc add.commute add_diff_cancel_right' qp_cone_upper)
    hence "date (t B\<bullet>(j+2)) - date (t B\<bullet>j) \<le> 2*T\<^sub>m\<^sub>a\<^sub>x" 
      by simp
    hence "date (t B\<bullet>(j+2)) \<le> 2*T\<^sub>m\<^sub>a\<^sub>x + date (t B\<bullet>j)" 
      by simp
    moreover have "n * T\<^sub>m\<^sub>i\<^sub>n \<le> date (t A\<bullet>(i+n)) - date (t A\<bullet>i)"  
      using qp `n > 0` by (simp add: qp_cone_lower)
    ultimately show "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n < 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"  
      by simp
  qed


lemma qs_relax_sound:
  assumes qp:"quasiperiodic t"
  and "\<forall> t C p q. p < q \<longrightarrow> arrival (t C\<bullet>p) < arrival (t C\<bullet>q)"
  and "relax_discr f t"
  and "com A B"
  and "A \<noteq> B"
  and "n > 0"
  and "n * T\<^sub>m\<^sub>i\<^sub>n  + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"
  shows "\<not> (f B\<bullet>j \<le> f A\<bullet>i \<and> f A\<bullet>(i+n) \<le> f B\<bullet>(j+1))"
  proof 
    assume "(f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1))"
    hence "f B\<bullet>j \<le> f A\<bullet>i" 
    and "f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)" 
      by simp_all
    moreover from `n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x` Tmaxpos'
    have "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      by simp   
    ultimately show False
    proof (cases "f A\<bullet>(i+n) = f B\<bullet>(j+1)")
      assume "f A\<bullet>(i+n) = f B\<bullet>(j+1)"
      have "B\<bullet>(j+1) \<rightarrow>t B\<bullet>(j+2)"
        by (metis Suc_eq_plus1 add.commute add.left_commute hb1.simps 
        lessI one_add_one tranclp.r_into_trancl)
      with `relax_discr f t` have "f B\<bullet>(j+1) < f B\<bullet>(j+2)" 
        using relax_discr_def com_refl chb_def by simp
      with `f A\<bullet>(i+n) = f B\<bullet>(j+1)` have "f A\<bullet>(i+n) < f B\<bullet>(j+2)" 
        by simp
      with `relax_discr f t` `com A B` have "A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+2)" 
        using  relax_discr_def chb_def by simp
      moreover from `com A B` `relax_discr f t` `f B\<bullet>j \<le> f A\<bullet>i` have "\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j"
        by (simp add: f_relax_nhb)
      ultimately have "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n < 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"  
        using assms by (simp add: not_qs_relax_sound_case2)
      thus False 
        using `n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x` by simp
    next 
      assume "\<not> f A\<bullet>(i+n) = f B\<bullet>(j+1)"
      with `f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)` have "f A\<bullet>(i+n) < f B\<bullet>(j+1)" 
        by simp
      with `relax_discr f t` `com A B` have "A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+1)"
        using relax_discr_def chb_def by simp
      moreover from `com A B` `relax_discr f t` `f B\<bullet>j \<le> f A\<bullet>i` have "\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j"
        by (simp add: f_relax_nhb)
      ultimately have "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n < T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
        using assms by (simp add: not_qs_relax_sound_case1)
      thus False 
        using `n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x` by simp
    qed
  qed

subsection "Weakest condition"

lemma qs_relax_eg:
  assumes "\<forall> t C p q. p < q \<longrightarrow> arrival (t C\<bullet>p) < arrival (t C\<bullet>q)"
  and "A \<noteq> B"
  and "com A B"
  and "n > 0"
  and "\<not> (\<exists> t i j. quasiperiodic t
          \<and>  (\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j) \<and> (\<not> A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+1)) \<and> (A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+2)))"
  shows "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
  proof (rule ccontr)
    assume "\<not> n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"
    hence "\<exists> t i j.  quasiperiodic t  
           \<and>  (\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j) \<and> (\<not> A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+1)) \<and> (A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+2))"
    proof -
      from `\<not> n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x` obtain \<epsilon>
        where "\<epsilon> > 0"
        and "\<epsilon> = 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x - (n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n)"
          by simp
  
      def eg == "\<lambda>e :: event.
                 if node e = A \<and> act e = 0 then \<lparr> date = \<epsilon>, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>
            else if node e = B then \<lparr> date = \<tau>\<^sub>m\<^sub>a\<^sub>x + act e * T\<^sub>m\<^sub>a\<^sub>x, trans = \<tau>\<^sub>m\<^sub>a\<^sub>x \<rparr>
            else \<lparr> date = \<epsilon> + act e * T\<^sub>m\<^sub>i\<^sub>n, trans = \<tau>\<^sub>m\<^sub>i\<^sub>n \<rparr>"

      have "\<forall> e. trans (eg e) = \<tau>\<^sub>m\<^sub>i\<^sub>n \<or> trans (eg e) = \<tau>\<^sub>m\<^sub>a\<^sub>x" 
        using eg_def by simp
      hence "\<forall> e. \<tau>\<^sub>m\<^sub>i\<^sub>n \<le> trans (eg e) \<and> trans (eg e) \<le> \<tau>\<^sub>m\<^sub>a\<^sub>x" 
        using eg_def taubounds by simp 
      moreover have "\<forall> e. date (eg (step e)) - date (eg e) = T\<^sub>m\<^sub>i\<^sub>n
              \<or> date (eg (step e)) - date (eg e) = T\<^sub>m\<^sub>a\<^sub>x "
        using eg_def `A \<noteq> B` by simp
      hence "\<forall> e. T\<^sub>m\<^sub>i\<^sub>n \<le> date (eg (step e)) - date (eg e) 
               \<and> date (eg (step e)) - date (eg e) \<le> T\<^sub>m\<^sub>a\<^sub>x"
        using Tbounds by auto
      moreover have "\<forall> e. 0 \<le> date(eg e)" 
        using eg_def Tmaxpos Tminpos taumaxpos' `\<epsilon> > 0` by simp    
      ultimately have qp:"quasiperiodic eg" 
        using quasiperiodic_def by simp
     
      have b0:"date (eg B\<bullet>0) = \<tau>\<^sub>m\<^sub>a\<^sub>x"
      and b1:"date (eg B\<bullet>1) = T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"
      and b2:"date (eg B\<bullet>2) = 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
      and a0:"arrival (eg A\<bullet>0) = \<tau>\<^sub>m\<^sub>a\<^sub>x + \<epsilon>"
      and an:"arrival (eg A\<bullet>n) = \<epsilon> + n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n"
        using eg_def `A \<noteq> B` `n >0` by simp_all

      from `\<epsilon> = 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x - (n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n)` 
      have h:"\<epsilon> + n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n = 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
        by simp    

      from h an b2  have "arrival (eg A\<bullet>n) \<le> date (eg B\<bullet>2)" 
        by simp
      hence "A\<bullet>n \<hookrightarrow>eg B\<bullet>2" 
        using chb_def `com A B` hb_arrival by auto
      moreover from h an b1 Tmaxpos have "arrival (eg A\<bullet>n) > date (eg B\<bullet>1)" 
        by simp
      with qp assms(1) `A \<noteq> B` `com A B` have "\<not> A\<bullet>n \<hookrightarrow>eg B\<bullet>1" 
        using chb_def by (metis hb_realtime not_le) 
      moreover from a0 b0 `\<epsilon> >0` taumaxpos have "date (eg B\<bullet>0) < arrival (eg A\<bullet>0)" 
        by simp
      with qp assms(1) `A \<noteq> B` have "\<not> A\<bullet>0 \<hookrightarrow>eg B\<bullet>0" 
        using hb_realtime by force
      ultimately have "(\<not> A\<bullet>0 \<hookrightarrow>eg B\<bullet>0) \<and> (\<not> A\<bullet>n \<hookrightarrow>eg B\<bullet>1) \<and> (A\<bullet>n \<hookrightarrow>eg B\<bullet>2)" 
        by simp
      thus ?thesis 
        using qp  by (metis monoid_add_class.add.left_neutral)
    qed
    with assms(5) show False 
      by auto
  qed


lemma qs_relax_weakest:
  assumes "\<forall> t. quasiperiodic t \<longrightarrow> (\<exists> f. tight_discr f t)"
  and "\<forall> t C p q. p < q \<longrightarrow> arrival (t C\<bullet>p) < arrival (t C\<bullet>q)"
  and "com A B"
  and "A \<noteq> B"
  and "n > 0"
  and "\<not> (\<exists> t i j f. 
          quasiperiodic t \<and> 
          relax_discr f t \<and>
          (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)))"
  shows "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x" 
  proof (rule ccontr)
    assume "\<not> n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"
    with assms(2-5) 
    have "\<exists> t i j. 
            quasiperiodic t \<and>  
            (\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j) \<and> (\<not> A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+1)) \<and> (A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+2))"
      by (metis qs_relax_eg)
    then obtain t i j 
    where qp:"quasiperiodic t"
    and "(\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j)"
    and "(\<not> A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+1))"
    and "(A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+2))" 
      by auto 
    from qp assms(1) obtain f 
    where "tight_discr f t" 
      by auto 
    hence f_discr:"relax_discr f t" 
      using tight_discr_def by simp
    have "f B\<bullet>j \<le> f A\<bullet>i \<and> f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)"
    proof -
      from f_discr `(A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+2))` `com A B` have "f A\<bullet>(i+n) < f B\<bullet>(j+2)" 
        using relax_discr_def chb_def by auto
      moreover from f_discr `com A B` `\<not> (A\<bullet>(i+n) \<hookrightarrow>t B\<bullet>(j+1))`
      have "f A\<bullet>(i+n) \<ge> f B\<bullet>(j+1)" 
        using nhb_f_reflax by simp
      moreover have "B\<bullet>(j+1) \<hookrightarrow>t B\<bullet>(j+2)" 
        using chb_def hb_subsequent com_refl by (simp add:tranclp.r_into_trancl)
      with f_discr have "f B\<bullet>(j+1) < f B\<bullet>(j+2)" 
        using relax_discr_def chb_def com_refl by auto
      ultimately have "f A\<bullet>(i+n) = f B\<bullet>(j+1)" 
        using f_tight `tight_discr f t` `A \<noteq> B` `com A B` by simp
      moreover from f_discr `com A B` `(\<not> A\<bullet>i \<hookrightarrow>t B\<bullet>j)` have "f B\<bullet>j \<le> f A\<bullet>i" 
        by (rule nhb_f_reflax)
      ultimately show "(f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1))" 
        by simp
    qed
    with qp f_discr have "\<exists> t i j f. quasiperiodic t 
                  \<and> relax_discr f t
                  \<and> (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1) )" 
      by auto
    thus False 
      using assms(6) by auto
  qed


theorem qs_relax:
  assumes "\<forall> t. quasiperiodic t \<longrightarrow> (\<exists> f. tight_discr f t)"
  and "\<forall> t C p q. p < q \<longrightarrow> arrival (t C\<bullet>p) < arrival (t C\<bullet>q)"
  and "com A B"
  and "A \<noteq> B"
  and "n > 0"
  shows "(\<not> (\<exists> t i j f. quasiperiodic t \<and> 
           relax_discr f t  \<and> 
           (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1))))
       \<longleftrightarrow> n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"
  proof
    assume "\<not> (\<exists> t i j f. quasiperiodic t  
               \<and> relax_discr f t 
               \<and> (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)))"
    with assms show "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"
      by (rule qs_relax_weakest)
  next
    assume "n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n \<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x"
    show "\<not> (\<exists> t i j f. quasiperiodic t  
             \<and> relax_discr f t
             \<and> (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)))"
    proof
    assume "(\<exists> t i j f. quasiperiodic t  
                 \<and> relax_discr f t
                 \<and> (f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i+n) \<le> f B\<bullet>(j+1)))"
    then obtain t i j f
    where qp:"quasiperiodic t"
    and "relax_discr f t"
    and "(f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i + n) \<le> f B\<bullet>(j + 1))" 
      by auto
    with `relax_discr f t` qp assms(2-5) `n * T\<^sub>m\<^sub>i\<^sub>n + \<tau>\<^sub>m\<^sub>i\<^sub>n\<ge> 2*T\<^sub>m\<^sub>a\<^sub>x + \<tau>\<^sub>m\<^sub>a\<^sub>x` 
    have "\<not> (f B\<bullet>j \<le> f A\<bullet>i \<and> f A\<bullet>(i+n) \<le> f B\<bullet>(j+1))" 
      using qs_relax_sound by auto 
    with `(f B\<bullet>j \<le> f A\<bullet>i \<and>  f A\<bullet>(i + n) \<le> f B\<bullet>(j + 1))` show False 
      by simp
    qed
  qed

end
end %invisible
