theory FHG_th
  imports Main HOL.Real
begin

definition pref :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) => bool" where
"pref S r \<equiv> let r_as_set = {(a,b). r a b \<and> a \<in>S \<and> b\<in>S} in
 refl_on S r_as_set \<and> total_on S r_as_set \<and> trans r_as_set"

locale Hedonic_game =
  fixes N :: "'a set"          
  and pref_rel  :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" ("_ \<succeq>\<^sub>_ _" [60,61,60])
assumes "finite N"                
and   "\<forall>i\<in>N. pref {S. S \<subseteq> N \<and> i \<in> S} (\<lambda>x y. pref_rel x i y) "
begin                                  

definition isPartition :: "('a \<Rightarrow> 'a set) \<Rightarrow> bool" where
"isPartition \<pi> \<equiv> equiv N {(i,j). i \<in> N \<and> j \<in> \<pi> i}"
                                        
definition strict_pref_rel  :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" ("_ \<succ>\<^sub>_ _" [60,61,60]) where
"S \<succ>\<^sub>i T \<equiv> S \<succeq>\<^sub>i T \<and> \<not> ( T \<succeq>\<^sub>i S) "

                            
definition blocking_coalition :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> bool" where
"blocking_coalition \<pi> S \<equiv> (S\<noteq> {}) \<and> (S \<subseteq> N) \<and> (\<forall>i \<in> S. S \<succ>\<^sub>i \<pi> i)"
                                           
definition grand_coalition:: "'a \<Rightarrow> 'a set" where
"grand_coalition i = N"

definition weakly_blocking_coalition :: "('a \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> bool" where
"weakly_blocking_coalition \<pi> S \<equiv> (\<exists>i\<in>S. S \<succ>\<^sub>i \<pi> i) \<and> (\<forall>i\<in>S. S \<succeq>\<^sub>i \<pi> i)"
              
definition valid_partition :: "('a \<Rightarrow> 'a set) \<Rightarrow> bool" where
"valid_partition \<pi> \<equiv> (\<forall>x\<in>N. x \<in> \<pi> x \<and> \<pi> x \<subseteq> N) \<and> (\<forall>x\<in>N. \<forall>y\<in>N. x \<in> \<pi> y \<longrightarrow> \<pi> y = \<pi> x) "

definition to_partition :: "('a * 'a) set \<Rightarrow> 'a \<Rightarrow> 'a set" where 
"to_partition R x \<equiv> {y. (x,y) \<in> R }"

lemma  equiv_valid_partition:"equiv N R \<Longrightarrow> valid_partition (to_partition R)"
  unfolding valid_partition_def to_partition_def 
    equiv_def refl_on_def sym_def trans_def
  by blast

lemma to_partition_inv: " to_partition {(x,y). y \<in> \<pi> x} = \<pi>"
  unfolding to_partition_def by blast

lemma equiv_from_valid_partition: "valid_partition \<pi> \<Longrightarrow> equiv N {(x,y)\<in> N\<times>N .  y \<in> \<pi> x}"
  unfolding valid_partition_def equiv_def refl_on_def sym_def trans_def
  by blast 

definition in_core :: "('a \<Rightarrow> 'a set) \<Rightarrow> bool" where
"in_core \<pi> \<equiv>  \<not>(\<exists>S. blocking_coalition \<pi> S)"

definition core ::"('a \<Rightarrow> 'a set) set" where 
"core \<equiv> {\<pi>. valid_partition \<pi> \<and> in_core \<pi>}"
                                
definition weak_core :: "('a \<Rightarrow> 'a set) set" where
"weak_core \<equiv> {\<pi>. \<not>(\<exists>S. weakly_blocking_coalition \<pi> S)}"  
      
end
                                  
locale FHG =                     
  fixes N :: "'a set"
    and v:: "'a \<Rightarrow> 'a \<Rightarrow> real"      
  assumes finite:"finite N"        
begin                                        
                                   
definition val :: "'a \<Rightarrow> 'a set \<Rightarrow> real" ("v\<^sub>_ _" [60, 60]) where
"val i S \<equiv> sum (v i) S / card S "
                                
sublocale Hedonic_game N "(\<lambda>x i y. val i x \<ge> val i y)" 
  using finite by  unfold_locales     
    (auto simp add: pref_def refl_on_def total_on_def trans_def)
end           

locale simple_FHG =
  fixes N :: "'a set"
    and v:: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes finite:"finite N" 
begin
sublocale  FHG N "(\<lambda>x y. if v x y then 1 else 0 )"
  using finite by unfold_locales
end                                    
                    
locale sym_FHG = FHG + assumes sym :"\<forall>x y. v x y = v y x"  
                   
locale sym_simple_FHG = simple_FHG + assumes sym :"\<forall>x y. v x y = v y x"  

locale graph_FHG =      
  fixes N :: "'a set"                             
  and v:: "('a * 'a) set" 
assumes finite: "finite N"
and sym: "sym v"
and valid_edges: "v \<subseteq> N \<times> N"
begin                  
sublocale sym_simple_FHG N "\<lambda>x y. (x,y) \<in> v"
proof unfold_locales
  show "finite N" using finite .
  show "\<forall>x y. ((x, y) \<in> v) = ((y, x) \<in> v)"
    by (meson local.sym symE) 
qed 
definition neighbors :: "'a \<Rightarrow> 'a set" where
"neighbors x \<equiv> {y. (x,y) \<in> v} "

definition val_graph :: "'a \<Rightarrow> 'a set \<Rightarrow> real" where
"val_graph i S \<equiv> card (S \<inter> neighbors i) / card S"


lemma val_graph_correct:
  assumes "finite S"
  shows "val_graph i S = val i S" 
proof -                         
  from assms have "card (S \<inter> neighbors i) = (\<Sum>y\<in>S. if (i, y) \<in> v then 1 else 0)"
    unfolding neighbors_def
    by (smt (verit, best) card_eq_sum mem_Collect_eq sum.cong sum.inter_restrict) 
  hence "real(card (S \<inter> neighbors i)) = real(\<Sum>y\<in>S. if (i, y) \<in> v then 1 else 0)"
    by simp                                     
  moreover have "... = (\<Sum>y\<in>S. if (i, y) \<in> v then 1 else  0)"
    by (auto  simp add: if_distrib)  (meson of_nat_0 of_nat_1)
  ultimately show ?thesis  unfolding val_graph_def val_def  by presburger                                              
qed                              
  
 
               
end                  
                           
subsection "Example"                                       

definition N\<^sub>0_list :: "nat list" where 
"N\<^sub>0_list \<equiv> [1,2,3,4,5,6]"
       
definition E\<^sub>0_list :: "(nat * nat) list" where "E\<^sub>0_list \<equiv> [(1,2),(1,3),(1,4),(2,1),(2,3),(2,5),(3,1),(3,2),(3,6),(4,5)
,(4,6),(4,1),(5,4),(5,6),(5,2),(6,4),(6,5),(6,3) 
]"

fun elem :: " 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
"elem x [] = False"|                
"elem x (y#ys) = (x=y \<or> elem x ys)"    

fun rem :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"rem x [] = []"|
"rem x (y#ys) = (if x =y then rem x ys else y# rem x ys)" 
                                                      
lemma len_rem_decreasing:"length (rem (b, a) xs) \<le> (length xs)"
  by (induction xs) auto
          
function isSym :: "('a * 'a) list \<Rightarrow> bool" where
"isSym [] = True"|
"isSym ((a,b)#xs) = (if elem (b,a) xs then  isSym (rem (b,a) xs) else False)"
by pat_completeness auto
termination isSym   
proof (relation "measure length")
  show "wf (measure length)" by simp 
  show " \<And>a b xs.
       elem (b, a) xs \<Longrightarrow>
       (rem (b, a) xs, (a, b) # xs) \<in> measure length"
using len_rem_decreasing         
  by (metis in_measure le_imp_less_Suc length_Cons)
qed
                            
lemma elem_correct:"elem x xs = (x \<in> set xs)"
  by (induction xs) auto                        

lemma rem_correct: "set (rem x xs) = set xs - {x}"
  by (induction xs) auto         
                 
lemma sym_larger: "sym S \<Longrightarrow> sym (insert (b,a) (insert (a,b) S))"
  using sym_def by auto

lemma sym_correct: "isSym xs \<Longrightarrow> sym (set xs)"
proof (induction xs rule: isSym.induct)
  case 1
then show ?case unfolding sym_def by simp
next
  case (2 a b xs)
  hence *:"elem (b,a) xs" "isSym (rem (b, a) xs)"
    by (meson isSym.simps(2)) +
  hence "sym (set (rem (b, a) xs))" using 2 by simp
  hence t:"sym (set xs - {(b,a)}) " by (simp add: rem_correct)
  moreover have "set ((a,b)#xs)  = insert (a,b) (insert (b,a) (set xs - {(b,a)}))"
    by (metis "*"(1) elem_correct insert_Diff list.simps(15))
  ultimately show ?case unfolding sym_def
    by (metis t symE sym_larger) 
qed

locale imp_graph_FHG =           
  fixes N :: "'a list"
  and v:: "('a * 'a) list"                            
assumes isSym_v: "isSym v"
and distinct_players: "distinct N"
and valid_edges: "set v \<subseteq> set N \<times> set N"
begin                            
sublocale graph_FHG "set N" "set v"     
  using isSym_v sym_correct valid_edges by unfold_locales auto
                           
definition valuation :: "'a \<Rightarrow> 'a list \<Rightarrow> real" where
"valuation i S = length (filter (\<lambda>x. elem (i,x) v) S) / length S"
                                     
lemma valuation_correct:                               
  assumes "distinct S"     
  shows "valuation i S = val i (set S)"
proof -                              
  have "length S = card (set S)"   
    by (simp add: assms distinct_card)
  moreover have "length (filter (\<lambda>x. elem (i, x) v) S) 
    = sum (\<lambda>y. if (i, y) \<in> set v then 1 else 0) (set S) "
    using assms elem_correct 
    by (induction S) (auto simp add: elem_correct)
  ultimately show ?thesis 
    unfolding valuation_def val_def
    by (smt (verit) of_nat_0 of_nat_1 of_nat_sum sum.cong)
qed
                            
definition prefer_comp :: "'a \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> bool" where 
"prefer_comp x xs \<pi> = ((valuation x xs) > (valuation x (\<pi> x))) "
                                                
lemma prefer_comp_correct:     
  assumes "distinct (\<pi> x)"
  and "distinct xs"       
shows
 "prefer_comp x xs \<pi> = (strict_pref_rel (set xs) x ( set (\<pi> x)))"
  unfolding prefer_comp_def strict_pref_rel_def
  using valuation_correct assms by auto   

definition all :: "bool list \<Rightarrow> bool" where 
"all xs = foldl (\<and>) True xs "

lemma all_correct_aux: "foldl (\<and>) I xs = (I \<and> (\<forall>x\<in>set xs. x))"
  by (induction xs arbitrary: I) auto
               
lemma all_correct: "all xs = (\<forall>p \<in> set xs. p)"
  unfolding all_def using all_correct_aux by auto                  

                        
definition isBlocking :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> bool" where
"isBlocking xs \<pi> = (xs \<noteq> [] \<and>  all (map (\<lambda>x. prefer_comp x xs \<pi>) xs))"
                                               
lemma isBlocking_correct:                          
  assumes "\<forall>x. distinct (\<pi> x)"         
  and "distinct xs" 
  and "set xs \<subseteq> set N"
shows "isBlocking xs \<pi> = blocking_coalition (set o \<pi>)  (set xs)"
 unfolding blocking_coalition_def isBlocking_def apply auto 
  using list.set_sel(1) all_correct prefer_comp_correct assms    
  by auto                       

fun all_possible_coalitions :: " 'a list \<Rightarrow> 'a list list" where
"all_possible_coalitions [] = [[]] " |                         
"all_possible_coalitions (x #xs) = 
(let res = all_possible_coalitions xs in res @ map ((#)x) res)"
                               
lemma all_possible_coalitions_correct:        
"distinct xs \<Longrightarrow>set (map set (all_possible_coalitions xs)) = {x. x \<subseteq> set xs}"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)   
  show ?case    
  proof 
    show "set (map set (all_possible_coalitions (a # xs)))
    \<subseteq> {x. x \<subseteq> set (a # xs)}" 
    proof 
      fix x
      assume "x \<in> set (map set (all_possible_coalitions (a # xs)))"
      then show "x \<in> {x. x \<subseteq> set (a # xs)}"
        using Cons by (cases "a \<in> x") (auto simp add: Let_def)  
    qed     
    show "{x. x \<subseteq> set (a # xs)}
    \<subseteq> set (map set (all_possible_coalitions (a # xs)))"  
    proof                               
      fix x
      assume "x \<in> {x. x \<subseteq> set (a # xs)}"   
      hence " (\<exists>y\<subseteq> set xs. x = insert a y) \<or> x \<subseteq> set xs"
        using subset_insert by auto                           
      then show  "x \<in> set (map set (all_possible_coalitions (a # xs)))"
      proof   
        assume "\<exists>y\<subseteq>set xs. x = insert a y"
        then obtain y where "y \<subseteq> set xs" "x = insert a y"
          by blast 
        then show ?thesis                            
        using Cons by (auto simp add:Let_def)       
         (metis imageI image_image mem_Collect_eq) 
    next
      assume "x \<subseteq> set xs"
      then show ?thesis  using Cons by (auto simp add:Let_def)
    qed
  qed
qed         
qed                    

corollary all_possible_coalitions_co:                                      
 " distinct xs \<Longrightarrow> ys \<in> set (all_possible_coalitions xs) \<Longrightarrow> set ys \<subseteq> set xs "
  using all_possible_coalitions_correct by auto  
lemma distinct_coalitions: "distinct xs \<Longrightarrow> distinct (all_possible_coalitions xs)"
proof (induction xs)
  case Nil             
  then show ?case by auto
next                                         
  case (Cons a xs)    
  then show ?case
    using all_possible_coalitions_co by (auto simp add: Let_def distinct_map ) force
qed                      

lemma coalition_is_distinct: 
"distinct xs \<Longrightarrow> x \<in> set (all_possible_coalitions xs) \<Longrightarrow> distinct x"
  apply (induction xs arbitrary:x)
  using all_possible_coalitions_co apply (auto simp add: Let_def) by auto   
                                
             

definition is_in_core :: "('a \<Rightarrow> 'a list) \<Rightarrow> bool" where
"is_in_core \<pi> \<equiv> all (map (\<lambda>xs. \<not> (isBlocking xs \<pi>)) (all_possible_coalitions N))"
             
lemma helper: "\<lbrakk>(\<forall>x \<in>set xs.  set x \<subseteq> set N); (\<forall>x \<in>set xs. distinct x); \<forall>x. distinct( \<pi> x)\<rbrakk> \<Longrightarrow> map (\<lambda>x. \<not> isBlocking x \<pi>) xs =  map (\<lambda>x.\<not> blocking_coalition (set o \<pi>) (set x)) xs"
  apply (induction xs)
  using isBlocking_correct by auto

lemma helper2:"S \<in> set( map set xs) \<Longrightarrow> \<exists>l. set l = S "
  by (induction xs) auto  

lemma is_in_core_correct:                   
  assumes "\<forall>x. distinct( \<pi> x)"
  shows
"is_in_core \<pi> = in_core (set o \<pi>)"
  unfolding is_in_core_def in_core_def all_correct 
proof                      
  assume asm: "\<forall>p\<in>set (map (\<lambda>xs. \<not> isBlocking xs \<pi>)
              (all_possible_coalitions N)).      
       p"                                    
  hence  * :"\<forall>p\<in>set (map (\<lambda>xs. \<not> blocking_coalition (set o \<pi>) (set xs))
(all_possible_coalitions N)).p"            
    using helper coalition_is_distinct
    all_possible_coalitions_co assms distinct_players by force  
  have "\<forall>S. \<not> blocking_coalition (set o \<pi>) S "  
  proof 
    fix S                         
    show " \<not> blocking_coalition (set o \<pi>) S"
    proof(cases "S \<subseteq> set N")
      case True 
      hence "S \<in>set (map set (all_possible_coalitions N))"
        using all_possible_coalitions_correct distinct_players by blast
      then obtain l where l_def: " l \<in> set (all_possible_coalitions N)"  "set l = S"
        using helper2 by auto   
      hence "\<not> blocking_coalition (set o \<pi>) (set l)"
        using *  by force                 
      thus ?thesis using l_def(2) by simp                
    next                        
      case False                                                    
      then show ?thesis                                             
        unfolding blocking_coalition_def by auto                         
    qed                                                           
  qed  
  then show " \<nexists>S. blocking_coalition (set o \<pi>) S" by auto
next                                                 
  assume asm:"\<nexists>S. blocking_coalition (set o \<pi>) S"    
  show "\<forall>p\<in>set (map (\<lambda>xs. \<not> isBlocking xs \<pi>)     
              (all_possible_coalitions N)). 
       p "       
  proof 
    fix p      
    assume "p \<in>  set (map (\<lambda>xs. \<not> isBlocking xs \<pi>)
                   (all_possible_coalitions N))"
    then obtain l where l_def: "l \<in> set (all_possible_coalitions N)" " p = (\<not>isBlocking l \<pi>) "
      by auto                                  
    hence "p = (\<not> blocking_coalition (set o \<pi>) (set l) )"
      using all_possible_coalitions_co assms coalition_is_distinct distinct_players
          isBlocking_correct by presburger
    then show p using asm by auto                                                       
  qed
qed

fun isDistinct :: "'a list \<Rightarrow> bool" where
"isDistinct [] = True" |
"isDistinct (x#xs) = (\<not> elem x xs \<and> isDistinct xs)"

lemma isDistinct_correct:"distinct xs = isDistinct xs "                
using elem_correct  by (induction xs) fastforce+  
                                                  
                                                   
end                                               
                    
locale example_1
begin                                                             
interpretation imp_graph_FHG "N\<^sub>0_list" "E\<^sub>0_list"      
  unfolding N\<^sub>0_list_def by unfold_locales  (auto simp add: E\<^sub>0_list_def)


lemma th1: "isBlocking  [Suc 0::nat,2,3] (\<lambda>_. N\<^sub>0_list)"  
  unfolding isBlocking_def all_def prefer_comp_def valuation_def
  unfolding  E\<^sub>0_list_def  N\<^sub>0_list_def by auto  
                                
lemma "blocking_coalition (\<lambda>_. set N\<^sub>0_list) {1,2,3}"  
proof -                                         
  have "distinct [1::nat,2,3]" using isDistinct_correct by auto
  moreover have "\<forall>x. distinct ( (\<lambda>_. N\<^sub>0_list) x)"
    by (simp add: distinct_players) 
  ultimately show ?thesis using th1 isBlocking_correct[of "(\<lambda>_. N\<^sub>0_list)" "[1, 2, 3]" ]
    by (auto simp add:N\<^sub>0_list_def comp_def)  

qed             

abbreviation "f \<equiv> (\<lambda>x. if x \<le> 3 then [1::nat,2,3] else [4,5,6])"
lemma is_in_core:"is_in_core f "
  unfolding is_in_core_def isBlocking_def all_def
  unfolding N\<^sub>0_list_def  prefer_comp_def        
  apply auto
  unfolding valuation_def apply auto
  unfolding E\<^sub>0_list_def apply auto
  done        

lemma core: "(set o f) \<in> core" 
proof -
  have "\<forall>x. distinct (f x)" by auto
  hence "in_core (set o f)"                  
    using is_in_core_correct[of f] is_in_core  by auto
  moreover have "valid_partition (set o f)"
    unfolding valid_partition_def
    unfolding N\<^sub>0_list_def by auto
  ultimately show ?thesis unfolding core_def by auto
qed                                     
                   
       
                                    


end                          

locale example_2
begin
                                   
datatype ClusterType = A | B | C 

datatype ClusterNumber = O1 | O2 | O3 | O4 | O5 

fun Suc :: "ClusterNumber \<Rightarrow> ClusterNumber" where 
"Suc O1 = O2"|
"Suc O2 = O3"|
"Suc O3 = O4"|
"Suc O4 = O5"|      
"Suc O5 = O1"

fun pred :: "ClusterNumber \<Rightarrow> ClusterNumber" where
"pred O1 = O5"|
"pred O2 = O1"|
"pred O3 = O2"|
"pred O4 = O3"|
"pred O5 = O4"
                     
lemma pred_suc[simp]:"pred(Suc x) = x"       
  by (cases x) auto      

lemma suc_pred[simp]:"Suc (pred x) = x"       
  by (cases x) auto

datatype Cluster = Cluster ClusterType ClusterNumber
             
datatype Node = Node Cluster nat

fun clusterNodes :: "Cluster \<Rightarrow> Node set" where            
"clusterNodes (Cluster A i) =  (\<lambda>n. Node (Cluster A i) n) `{1,2,3}"|
"clusterNodes (Cluster B i) =  (\<lambda>n. Node (Cluster B i) n) `{1,2}"|
"clusterNodes (Cluster C i) =  (\<lambda>n. Node (Cluster C i) n) `{1,2,3}"

fun clusterNodesList :: "Cluster \<Rightarrow> Node list" where 
"clusterNodesList (Cluster A i) =  map (\<lambda>n. Node (Cluster A i) n) [1,2,3]"|
"clusterNodesList (Cluster B i) =  map (\<lambda>n. Node (Cluster B i) n) [1,2]"|
"clusterNodesList (Cluster C i) =  map (\<lambda>n. Node (Cluster C i) n) [1,2,3]"

lemma distinct_clusterNodesList :"distinct (clusterNodesList x)"
  by (induct x rule: clusterNodesList.induct) auto
lemma clusterNodesList_set : "set (clusterNodesList x) = clusterNodes x"
  by (induct x rule: clusterNodesList.induct) auto

lemma finite_clusterNodes: "finite (clusterNodes x)"
  by (induct  x rule:clusterNodes.induct) auto

fun clusterEdge :: "Cluster \<Rightarrow> Cluster \<Rightarrow> bool" where
"clusterEdge (Cluster A i) (Cluster A j) = (i=j)"|
"clusterEdge (Cluster A i) (Cluster B j) = (i=j \<or> Suc j = i)"|
"clusterEdge (Cluster A i) (Cluster C j) = (i=j)"|
"clusterEdge (Cluster B i) (Cluster A j) = (i=j \<or> Suc i = j)"|
"clusterEdge (Cluster B i) (Cluster B j) = (i=j)"|
"clusterEdge (Cluster B i) (Cluster C j) = (Suc (Suc i) = j)"|
"clusterEdge (Cluster C i) (Cluster A j) = (i=j)"|
"clusterEdge (Cluster C i) (Cluster B j) = (Suc (Suc j) = i)"|
"clusterEdge (Cluster C i) (Cluster C j) = (i=j)"  
  
abbreviation vertices :: "Node set" where
"vertices \<equiv> \<Union> (clusterNodes ` UNIV) "   
fun edge :: "Node \<Rightarrow> Node \<Rightarrow> bool" where 
"edge (Node c1 i) (Node c2 j) = ((Node c1 i)\<noteq> (Node c2 j)\<and> clusterEdge c1 c2)"
                                 
abbreviation edges :: "(Node * Node) set" where
"edges \<equiv> {(i,j). i \<in> vertices \<and> j \<in> vertices \<and> edge i j }"

lemma finite_vertices:"finite vertices"
proof -
have "(UNIV::ClusterType set) = {A,B,C} "
    by (smt (verit) UNIV_eq_I example_2.ClusterType.exhaust insertI1 insert_commute)                    
  hence "finite (UNIV::ClusterType set)"
    by (metis finite.emptyI finite.insertI) 
  moreover have "(UNIV :: ClusterNumber set) = {O1,O2,O3,O4,O5}"
    by (smt (verit) UNIV_eq_I example_2.ClusterNumber.exhaust insertI1 insert_commute)
  hence "finite (UNIV :: ClusterNumber set)" 
    by (metis finite.emptyI finite.insertI)  
  moreover have "(UNIV :: Cluster set) =  (\<lambda>(a,b). Cluster a b) ` ((UNIV::ClusterType set) \<times> (UNIV :: ClusterNumber set)) "
    by (metis UNIV_Times_UNIV UNIV_eq_I example_2.Cluster.exhaust rangeI split_conv)                                             
  ultimately have "finite (UNIV:: Cluster set)"
    by (smt (verit) UNIV_Times_UNIV finite_Prod_UNIV finite_imageI) 
  moreover have "\<forall>x. finite (clusterNodes x)"   
    by (metis clusterNodes.elims finite.emptyI finite_imageI finite_insert) 
  ultimately show  "finite vertices"  by blast
qed
  
interpretation graph_FHG vertices edges      
proof unfold_locales 
  show  "finite vertices" using finite_vertices .                   
next                                                   
  show "sym edges"                                              
    unfolding sym_def                                        
    by (auto elim!: edge.elims clusterEdge.elims)
next
  show "edges \<subseteq> vertices \<times> vertices " by blast
qed  
                                    
fun neighboring_clusters :: "Cluster \<Rightarrow> Cluster set" where 
"neighboring_clusters (Cluster A x) = {Cluster A x, Cluster B x, Cluster B (pred x), Cluster C x}"|
"neighboring_clusters (Cluster B x) = {Cluster A x, Cluster A (Suc x), Cluster B x, Cluster C (Suc ( Suc x))}"|
"neighboring_clusters (Cluster C x) = {Cluster A x, Cluster B (pred (pred x)), Cluster C x }"

lemma neighboring_clusters_correct : "neighboring_clusters x = {y. clusterEdge x y}"
  apply (auto elim!: edge.elims neighboring_clusters.elims clusterEdge.elims
      simp add: pred_suc)
  apply (rule neighboring_clusters.cases[of x])
  using pred_suc suc_pred by auto

lemma cluster_correct:
  assumes
"Node(Cluster T i) n \<in> vertices"
shows " Node(Cluster T i) n \<in> clusterNodes (Cluster T i)"
proof -
  have  "\<And>x. (Node (Cluster T i) n \<in> clusterNodes x \<longrightarrow>
         Node (Cluster T i) n \<in> clusterNodes (Cluster T i))"
    subgoal for x
      apply (cases x)
      apply (auto)
      subgoal for T' i'
        apply(cases T'; cases i')
                      apply auto
        done
      done
    done
  thus ?thesis using assms by auto
qed
lemma node_in_cluster:"Node c n \<in> clusterNodes c' \<Longrightarrow> c= c'"
  apply (cases c; cases c')
  subgoal for x _ y _
    apply(cases x; cases y)
            apply (auto)
    done
  done
lemma  neighbors_correct:
  assumes "Node c n  \<in> vertices"
  shows "neighbors (Node c n) = \<Union> (clusterNodes ` (neighboring_clusters c)) - {Node c n}"
proof
  show "neighbors (Node c n) \<subseteq> \<Union> (clusterNodes ` neighboring_clusters c) - {Node c n}"
  proof
    fix x
    assume asm: "x \<in> neighbors (Node c n)"
    obtain cx nx where x_def :"x = Node cx nx" using Node.exhaust by blast
    hence "Node c n \<noteq> Node cx nx" "cx \<in> neighboring_clusters c"   "Node cx nx \<in> clusterNodes cx" 
      using asm neighbors_def node_in_cluster neighboring_clusters_correct by fastforce+
    thus "x \<in> \<Union> (clusterNodes ` neighboring_clusters c) - {Node c n}"
      using x_def by blast
  qed
next
  show "\<Union> (clusterNodes ` neighboring_clusters c) - {Node c n} \<subseteq> neighbors (Node c n)"
  proof
    fix x
    assume asm: "x \<in> \<Union> (clusterNodes ` neighboring_clusters c) - {Node c n}"
    obtain cx nx where x_def :"x = Node cx nx" using Node.exhaust by blast
    hence "Node c n \<noteq> Node cx nx" "clusterEdge c cx"   "Node cx nx \<in> clusterNodes cx" 
      using asm neighbors_def node_in_cluster neighboring_clusters_correct by fastforce +
    thus  "x \<in> neighbors (Node c n) " 
      using assms graph_FHG.neighbors_def graph_FHG_axioms x_def by fastforce
  qed
qed

lemma neighbors_correct_set:
  assumes "x \<in> clusterNodes c"
  shows "neighbors x = \<Union> (clusterNodes ` (neighboring_clusters c)) - {x}"
  using assms neighbors_correct 
  by (smt (verit, ccfv_SIG) UNIV_I UN_iff example_2.Node.exhaust node_in_cluster)
lemma inter_set_card:
  assumes  "\<forall>x y. x \<noteq> y \<longrightarrow>  (f x \<inter> f y) = {}"
  and "x \<notin> F"
shows "f x \<inter> \<Union> (f ` F) = {}"
  apply (rule ccontr)
  using assms apply auto
  by (metis disjoint_iff)
lemma card_union:
  assumes "\<forall>x. c x = card (f x)"
    and "\<forall>x y. x \<noteq> y \<longrightarrow>  (f x \<inter> f y) = {}"
    and "finite S"
    and "\<forall>x. finite ( f x)"
  shows "card ( \<Union> (f ` S)) = sum c S"
proof (rule finite_induct )
  show "finite S" using assms(3) .
next
  show "card (\<Union> (f ` {})) = sum c {}" by auto
next
  fix x F
  assume asm: "finite F" "x \<notin> F" "card (\<Union> (f ` F)) = sum c F"
  have "card (f x \<union> \<Union> (f ` F)) = card (f x) + card ( \<Union> (f ` F))"
    using assms(2) assms(4) inter_set_card asm(2) 
    by (metis asm(1) card_Un_disjoint finite_UN)
  thus  "card (\<Union> (f ` insert x F)) = sum c (insert x F)"
    by (simp add: asm(1) asm(2) asm(3) assms(1))
qed

thm "card_Diff_singleton"

fun clusterCard :: "Cluster \<Rightarrow> nat" where
"clusterCard (Cluster A _) = 3"|   
"clusterCard (Cluster B _) = 2"|
"clusterCard (Cluster C _) = 3"  
                                                     
lemma clusterCard_correct: "clusterCard c = card (clusterNodes c)"
  by (induct  c rule:clusterNodes.induct) auto 




lemma clusterNodes_inter_empty:
  assumes "x \<noteq> y"
  shows "clusterNodes x \<inter> clusterNodes y = {}"
  using assms by (induct x y rule:clusterEdge.induct) auto

lemma finite_neighboring_clusters: "finite(neighboring_clusters c)"
  by(induct c rule: neighboring_clusters.induct)  auto

lemma in_neighboring: "c \<in> neighboring_clusters c"
  by (induct c rule: neighboring_clusters.induct)  auto

lemma neighbors_card:
  assumes "Node c n \<in> vertices"
  shows "card (neighbors (Node c n)) = sum clusterCard (neighboring_clusters c) - 1"
proof -
  have "card (\<Union> (clusterNodes ` neighboring_clusters c)) = sum clusterCard (neighboring_clusters c)"
    using card_union clusterCard_correct clusterNodes_inter_empty finite_clusterNodes  finite_neighboring_clusters
    by metis
  moreover have "Node c n \<in> \<Union> (clusterNodes ` neighboring_clusters c) " using assms 
    by (metis UN_iff in_neighboring node_in_cluster)
  ultimately show ?thesis using assms neighbors_correct by auto
qed

lemma pred_diff[simp]:"pred i \<noteq> i"
  by (cases i) auto

lemma suc_diff[simp]:"Suc i \<noteq> i"
  by (cases i) auto

corollary card_neighbors_A:
  assumes "Node (Cluster A i) n \<in> vertices"
  shows "card(neighbors (Node (Cluster A i) n)) = 9"
  using neighbors_card assms  apply auto
  apply( subst sum.insert)
    apply (auto)
  using pred_diff by metis 

corollary card_neighbors_A':
  fixes x l
  assumes "x \<in> clusterNodes (Cluster A l)"
  shows "card (neighbors x) = 9"
proof -
  obtain n where "x = Node (Cluster A l) n" using assms by auto
  thus ?thesis using  card_neighbors_A assms by blast
qed

                                               
corollary card_neighbors_B:
  assumes "Node (Cluster B i) n \<in> vertices"
  shows "card(neighbors (Node (Cluster B i) n)) = 10"
  using neighbors_card assms  apply auto
  apply( subst sum.insert)
    apply (auto)
  using suc_diff by metis

corollary card_neighbors_B':
  fixes x l
  assumes "x \<in> clusterNodes(Cluster B l)"
  shows "card(neighbors x) = 10"
proof -
  obtain n where "x = Node (Cluster B l) n" using assms clusterNodes.simps(2) by blast
  thus ?thesis using card_neighbors_B assms by blast
qed

corollary card_neighbors_C:
  assumes "Node (Cluster C i) n \<in> vertices"
  shows "card(neighbors (Node (Cluster C i) n)) = 7"
  using neighbors_card assms  by auto

corollary card_neighbors_C':
  fixes x l
  assumes "x \<in> clusterNodes (Cluster C l)"
  shows "card (neighbors x) = 7"
proof -
  obtain n where "x = Node (Cluster C l) n" using assms clusterNodes.simps(3) by blast
  thus ?thesis using  card_neighbors_C assms by blast
qed

  
                                                                                                            
lemma ex_clusterNode_intro: " Node c n \<in> clusterNodes c  \<Longrightarrow>    \<exists>x. Node c n \<in> clusterNodes x"
  by (rule HOL.exI)

lemma no_self_neighbor:"x \<notin> neighbors x"
  using example_2.edge.elims(1) neighbors_def by auto


definition f:: "nat \<Rightarrow> real" where
"f x \<equiv> x / (x+2)"
lemma mono_f: "mono f"
proof -
  have "\<forall>x. f x = 1 - 2/(x+2)"
    unfolding f_def apply (auto simp add:algebra_simps) 
    by (smt (verit, ccfv_SIG) add_divide_distrib divide_self_if of_nat_0_le_iff)
  thus "mono f" unfolding mono_def apply (auto) 
    by (simp add: frac_le)
qed

lemma  card_ratio:
  assumes  "finite y"
    and "card x \<le> (v::nat)"
    and "x \<subseteq> y"
    and "a \<in> y" "a \<notin> x"
    and "b \<in> y" "b \<notin> x"
    and "a \<noteq> b"
  shows "card x / card y \<le> (v/ (v+2))"
proof -
  have "finite x" using assms finite_subset by auto
  moreover  have "insert a ( insert b x) \<subseteq> y"
    using assms by auto
  ultimately have "card x + 2 \<le> card y" using card_mono assms 
    by (metis add_2_eq_Suc' card_insert_disjoint finite.insertI insert_iff) 
  hence "card x / card y \<le> f (card x)" unfolding f_def  using assms(3) by (auto simp add:frac_le)
  moreover have "...\<le> f v" using mono_f assms(2) unfolding mono_def by auto
  ultimately have  "card x / card y \<le>  (v/ (v+2))  " unfolding f_def by (auto simp add: algebra_simps)
  thus ?thesis   by (metis of_nat_add of_nat_numeral)
qed

value "(5::nat)/(6::nat)"

lemma finite_sup_aux:
  fixes g:: "'a \<Rightarrow> real"
  assumes "finite S"
  shows "S \<noteq> {} \<longrightarrow> (\<exists>x\<in>S. \<forall>y\<in>S. g y \<le> g x)"
using assms proof (rule finite_induct) 
  show "{} \<noteq> {} \<longrightarrow> (\<exists>x\<in>{}. \<forall>y\<in>{}. g y \<le> g x)" by auto
next
  fix x F
  assume asm: "finite F" " x \<notin> F" "F \<noteq> {} \<longrightarrow> (\<exists>x\<in>F. \<forall>y\<in>F. g y \<le> g x)"
  have "F = {} \<or> F \<noteq> {} " by auto
  then have "(\<exists>xa\<in>insert x F. \<forall>y\<in>insert x F. g y \<le> g xa)"
  proof
    assume "F = {}"
    hence "x\<in> insert x F\<and>( \<forall>y\<in>insert x F. g y \<le> g x)"  by auto
    thus ?thesis by auto
  next
    assume "F \<noteq> {}"
    then obtain x' where x'_def:  "x'\<in> F" "\<forall>y\<in>F. g y \<le> g x'"  using asm by auto
    have "g x' \<le> g x \<or>  g x \<le> g x'" by auto
    thus ?thesis
    proof 
      assume "g x' \<le> g x" 
      hence "x\<in> insert x F\<and>( \<forall>y\<in>insert x F. g y \<le> g x)" 
        using x'_def by auto
      thus ?thesis by auto
    next
      assume "g x \<le> g x'"
      hence "x' \<in>  insert x F\<and>( \<forall>y\<in>insert x F. g y \<le> g x')"
        using x'_def by auto
      thus ?thesis by auto
    qed
  qed
  thus "insert x F \<noteq> {} \<longrightarrow> (\<exists>xa\<in>insert x F. \<forall>y\<in>insert x F. g y \<le> g xa)" by auto
qed
       
lemma finite_sup:
  fixes g::"'a \<Rightarrow> real"
  assumes "finite S"
  and "S \<noteq> {}"
shows "\<exists>x\<in>S. \<forall>y\<in>S. g y \<le> g x"
  using finite_sup_aux assms by auto

definition f':: "nat \<Rightarrow> real" where
"f' x \<equiv> x / (x+1)"
lemma mono_f':
  fixes x y
  assumes "x < y"
  shows "f' x < f' y"
proof -
  have "\<forall>x. f' x = 1 - 1/(x+1)"
    unfolding f'_def apply (auto simp add:algebra_simps) 
    by (smt (verit, ccfv_SIG) add_divide_distrib divide_self_if of_nat_0_le_iff)
  thus "f' x < f' y" using assms by (auto simp add: frac_less2)
qed

lemma val_in_neighbors:
  assumes "finite S" "x \<in> S" "S- {x} \<subseteq> neighbors x"
  shows "val x S = f' (card (S -{x}))" 
proof -
  have "S \<inter> neighbors x = S - {x}" using assms no_self_neighbor by auto
  hence "val_graph x S = f' (card (S -{x})) " unfolding f'_def val_graph_def using assms(2) 
    by fastforce 
  thus ?thesis using val_graph_correct assms(1) by auto
qed

lemma subset_remove: "S \<subseteq> S' \<Longrightarrow> S - {x} \<subseteq> S' -{x}"
  by auto
lemma mono_val_fun:
  fixes x y z
  assumes "z > 0" "y>0" "x<y"
  shows "((x::nat)+(z::nat))/((y::nat)+z) > x/y"
proof -
  have "(x+z)*y > x*(y+z) " using assms 
    by (smt (verit, ccfv_SIG) add_mult_distrib mult.commute nat_add_left_cancel_less nat_mult_less_cancel_disj)
  hence "real ((x+z)*y) > real (x*(y+z))" using of_nat_less_iff by blast
  hence "real(x+z) * real y > real x * real (y+z)" by auto 
  thus ?thesis
    by (metis add.commute assms(2) of_nat_0_less_iff pos_divide_less_eq pos_less_divide_eq times_divide_eq_left trans_less_add2)
qed
lemma same_cluster_neighbors:
  fixes i
  assumes "i \<in> clusterNodes c"
  assumes "j \<in> clusterNodes c"
  shows "neighbors i \<union> {i} = neighbors j \<union> {j}"
proof -
  obtain ni where "i = Node c ni" using assms 
    by (metis example_2.Node.exhaust node_in_cluster)
  moreover obtain nj where "j = Node c nj" using assms
        by (metis example_2.Node.exhaust node_in_cluster)
  ultimately show ?thesis using neighbors_correct assms
    by (smt (verit, best) UN_I Un_insert_left Un_insert_right UnionI in_neighboring insert_Diff rangeI)
qed

lemma finite_neighbors:"finite (neighbors x)"
proof -
  have "neighbors x \<subseteq> vertices" 
    using graph_FHG.neighbors_def graph_FHG_axioms by fastforce
  thus ?thesis using finite_subset finite_vertices by auto
qed

lemma mono_in_neighbor:
  fixes S T
  assumes "S \<noteq> {}"
  and "T \<subseteq> neighbors x"
  and "T \<noteq> {}"
  and "S \<inter> T = {}"
  and "finite S"
  and "finite T"
  and  "\<not> S \<subseteq> neighbors x "
shows "strict_pref_rel (S \<union> T) x S"
proof -
  have "card T > 0" using assms(3) assms(6) by auto
  moreover have "card S> 0" using assms(1) assms(5) by auto
  moreover have  "S \<inter> neighbors x \<subset> S" using assms(7) by auto
  hence "card (S \<inter> neighbors x) < card S" using assms(5)  by (meson psubset_card_mono)
  ultimately have 
"(card  (S \<inter> neighbors x) +  card T) / (card S + card T) > card (S \<inter> neighbors x) / card S "
    using mono_val_fun by auto
  moreover have "(S\<union>T) \<inter> neighbors x = (S \<inter> neighbors x) \<union> T " using assms  by auto
  hence "card ((S\<union>T) \<inter> neighbors x) = card  (S \<inter> neighbors x) +  card T" using card_Un_disjoint[of "S \<inter> neighbors x" T]
    assms(4) assms(5) assms(6) by auto
  moreover have "card (S\<union>T) = card S + card T" using card_Un_disjoint[of S T]
    assms(4) assms(5) assms(6) by auto
  ultimately have "val_graph x (S \<union> T) > val_graph x S" unfolding val_graph_def by auto 
  thus ?thesis unfolding strict_pref_rel_def using val_graph_correct assms(5) assms(6) by auto
qed


  
  

lemma cluster_is_neighbors_neighbor:                                      
  fixes i x c
  assumes "i \<in> neighbors x \<union>{x}"
  and "x \<in> clusterNodes c"
shows "clusterNodes c -{i} \<subseteq> neighbors i"
proof -
  obtain ci n where "i = Node ci n"  "i \<in> clusterNodes ci" 
    using assms 
    by (smt (verit, del_insts) UN_iff Un_iff case_prod_conv edge.elims(2) edge.elims(3) mem_Collect_eq neighbors_def node_in_cluster singletonD)
  hence "ci \<in> neighboring_clusters c" using neighbors_correct assms 
    by (smt (verit, ccfv_SIG) UN_iff Un_insert_right in_neighboring insert_Diff neighbors_correct_set node_in_cluster sup_bot.right_neutral)
  hence "c \<in> neighboring_clusters ci" 
    by (smt (verit, best) Un_insert_right \<open>i = Node ci n\<close> assms(1) assms(2) case_prod_conv example_2.Node.exhaust example_2.edge.simps example_2.neighboring_clusters_correct insert_iff mem_Collect_eq neighbors_def node_in_cluster sup_bot.right_neutral sym_simple_FHG.sym sym_simple_FHG_axioms)
  thus ?thesis using neighbors_correct
    using \<open>i \<in> clusterNodes ci\<close> neighbors_correct_set by auto
qed

lemma finite_pi:
  fixes x
  assumes "valid_partition \<pi>"
    and "x \<in> vertices" 
  shows "finite (\<pi> x)"
  using assms by (meson finite_subset finite_vertices valid_partition_def)

lemma finite_pi':
  fixes x
  assumes "\<pi> \<in> core"
  and "x \<in> clusterNodes c"
shows "finite (\<pi> x)"
  using assms finite_pi 
  unfolding  core_def by auto

lemma in_its_partition:
  fixes x \<pi>
  assumes "\<pi> \<in> core"
  and "x \<in> clusterNodes c"
  shows "x \<in> \<pi> x"
  using assms unfolding valid_partition_def core_def by blast

lemma mono_in_neighbor_general:
  fixes \<pi> x i c S 
  assumes "\<pi> \<in> core"
  and "x \<in> clusterNodes c"
  and "S \<subseteq> clusterNodes c"
  and "i \<in> \<pi> x"
  and "\<not> S  \<subseteq>  \<pi> x"
  and "\<pi> x -{x} \<subseteq> neighbors x"
shows "strict_pref_rel (S \<union> (\<pi> x)) i ( \<pi> x)"
proof -
  have "\<pi> x \<noteq> {}" 
    using in_its_partition assms(4) by blast
  moreover  obtain n where x_def: "x = Node c n"
    using  assms(2) Node.exhaust node_in_cluster by (metis in_mono)
  hence "i \<in> neighbors x \<union> {x}"  using assms(4) assms(6) by blast
  hence  "clusterNodes c - {i} \<subseteq> neighbors i" using  cluster_is_neighbors_neighbor
    assms(2) assms(3) by blast
  hence "S -{i} \<subseteq> neighbors i " using assms(3) by blast
  hence "S - \<pi> x \<subseteq> neighbors i " using assms(4) by blast
  moreover have "S - \<pi> x \<noteq> {}" using assms by auto
  moreover have "\<pi> x \<inter> (S - \<pi> x) = {}" by auto
  moreover have "finite (\<pi> x)" using finite_pi' assms by auto
  moreover have "finite (S - \<pi> x)" using finite_clusterNodes finite_subset assms(3) by fast
  moreover have "i \<in> \<pi> x" "i \<notin> neighbors i" 
    using assms(4)  no_self_neighbor by auto
  hence " \<not> \<pi> x \<subseteq> neighbors i"  by blast
  ultimately show ?thesis using mono_in_neighbor[of "\<pi> x" "S - \<pi> x" i]
    by (smt (verit, best) DiffD2 Diff_empty Diff_insert0 Diff_subset Un_Diff_cancel Un_commute assms(3) insertE insert_Diff subsetD subsetI)
qed

lemma mono_in_neighbor':
  fixes \<pi> x i c 
  assumes "\<pi> \<in> core"
  and "x \<in> clusterNodes c"
  and "i \<in> \<pi> x"
  and "\<not> clusterNodes c  \<subseteq>  \<pi> x"
  and "\<pi> x -{x} \<subseteq> neighbors x"
shows "strict_pref_rel (clusterNodes c \<union> (\<pi> x)) i ( \<pi> x)"
proof -
  have "\<pi> x \<noteq> {}" 
    by (metis (no_types, lifting) UnionI assms(1) assms(2) core_def empty_iff mem_Collect_eq rangeI valid_partition_def)
  moreover  obtain n where x_def: "x = Node c n"
    by (metis assms(2) example_2.Node.exhaust node_in_cluster) 
  hence "i \<in> neighbors x \<union> {x}"  using assms(3) assms(5) by blast
  hence  "clusterNodes c - {i} \<subseteq> neighbors i" using  cluster_is_neighbors_neighbor
    assms(2) by presburger
  moreover have "clusterNodes c - \<pi> x \<noteq> {}" using assms by auto
  moreover have "\<pi> x \<inter> (clusterNodes c - \<pi> x) = {}" by auto
  moreover have "finite (\<pi> x)" using finite_pi' assms by auto
  moreover have "finite (clusterNodes c - \<pi> x)" using finite_clusterNodes finite_subset by force
  moreover have "i \<in> \<pi> x" "i \<notin> neighbors i" 
    using assms(3)  no_self_neighbor by auto
  hence " \<not> \<pi> x \<subseteq> neighbors i"  by blast
  ultimately show ?thesis using mono_in_neighbor[of "\<pi> x" "clusterNodes c - \<pi> x" i]
    by (smt (verit, best) DiffD2 Diff_empty Diff_insert0 Diff_subset Un_Diff_cancel Un_commute assms(3) insertE insert_Diff subsetD subsetI)
qed

lemma val_upper_bound:
  fixes \<pi>
  assumes " \<not> \<pi> x - {x} \<subseteq> neighbors x"
  and "\<pi> \<in> core"
  and "x \<in> clusterNodes c"
  shows "val x (\<pi> x) \<le>  f( card (neighbors x))"
proof -
  obtain y where y_def: "y\<in>\<pi> x"  "y \<notin> neighbors x"  "y \<noteq> x" using assms by auto
  have "card ( \<pi> x \<inter> neighbors x) \<le> card ( neighbors x)" 
    by (metis (mono_tags, lifting) card_mono finite_neighbors inf_le2)
  hence "card (\<pi> x \<inter> neighbors x)/ card (\<pi> x) \<le> card (neighbors x) /( card (neighbors x) + 2)"
    using card_ratio[of "\<pi> x" "\<pi> x \<inter> neighbors x" "card ( neighbors x)" x y ] finite_pi'[of \<pi> x c ] y_def no_self_neighbor[of x]  assms
            in_its_partition[of \<pi> x c ]  
    by (metis (no_types, lifting) Int_iff inf_le1 of_nat_add of_nat_numeral)
  thus ?thesis using val_graph_correct[of "\<pi> x" x] 
    by (metis (no_types, lifting) assms(2) assms(3) f_def finite_pi' graph_FHG.val_graph_def graph_FHG_axioms of_nat_add of_nat_numeral)
qed
                              
                                     
lemma blocking_coalition_cluster_general:                     
  fixes \<pi> x c S
  assumes "x \<in> clusterNodes c"
  and "S \<subseteq> clusterNodes c"
  and "\<pi> \<in> core"
  and "\<forall>y \<in> S. val x (\<pi> x) \<ge> val y (\<pi> y)"
  and "\<forall> i\<in>\<pi> x. strict_pref_rel (S \<union> \<pi> x) i (\<pi> x)"   
shows "blocking_coalition \<pi> (S \<union> \<pi> x)"
  unfolding blocking_coalition_def proof (standard;standard; goal_cases)
  case 1
  then show False 
    using assms(1) assms(3) in_its_partition by auto
next
  show "S \<union> \<pi> x \<subseteq> vertices" using assms(1) assms(2) assms(3) 
    by (smt (verit, ccfv_threshold) Sup_upper2 Un_least UnionI core_def mem_Collect_eq rangeI valid_partition_def)
  show  "\<forall>i\<in>S \<union> \<pi> x. strict_pref_rel (S \<union> \<pi> x) i (\<pi> i)"
  proof
    fix i
    let ?S = "S \<union> \<pi> x"
    assume "i \<in> S \<union> \<pi> x"
    then show " strict_pref_rel (S \<union> \<pi> x) i (\<pi> i)"
    proof
      assume asm_i:"i \<in> S"
      hence t:"neighbors i \<union> {i} = neighbors x \<union> {x}"
              using same_cluster_neighbors[of i c x] assms(1) assms(2) by  auto 
      hence "neighbors i = neighbors x \<union> {x} -{i} "
              using no_self_neighbor by auto
      hence "?S \<inter> neighbors i = (?S \<inter> (neighbors x \<union> {x})) -{i} " by auto
      moreover have "... = (?S \<inter> neighbors x) \<union> {x} -{i}" using assms(1) assms(3) in_its_partition by auto
      ultimately have *: "?S \<inter> neighbors i  = (?S \<inter> neighbors x)  \<union> {x} -{i}" by simp
       have "card (?S \<inter> neighbors i) = card (?S \<inter> neighbors x) "
            proof(cases "i = x")
              case True
              then show ?thesis by auto
            next
              case False
              then have "i \<in> neighbors x" using t by auto
              hence "i \<in> (?S \<inter> neighbors x) \<union> {x}"   using asm_i by blast
              moreover have "x \<notin> (?S \<inter> neighbors x)" using no_self_neighbor by blast
              hence "card ((?S \<inter> neighbors x)  \<union> {x}) = card (?S \<inter> neighbors x) + 1"
                using finite_neighbors[of x] finite_subset[of "?S \<inter> neighbors x" "neighbors x"]
                by force
              ultimately show ?thesis using no_self_neighbor  "*" by auto
            qed
            hence "val_graph x ?S  = val_graph i ?S" 
              unfolding  val_graph_def by presburger
            moreover have finite_S: "finite ?S" 
              using assms(1) assms(2) finite_subset finite_clusterNodes finite_pi' 
              assms(3) by auto
            ultimately have "val i ?S = val x ?S" using val_graph_correct by auto
            moreover  have x'_pi:"x \<in> \<pi> x" using assms(2) assms(1) assms(3) in_its_partition by blast
            hence "val x ?S > val x (\<pi> x)"  using assms(5) unfolding strict_pref_rel_def 
              by force
            moreover have "val x (\<pi> x)\<ge> val i (\<pi> i)" using assms(4) asm_i by blast
            ultimately show ?thesis unfolding strict_pref_rel_def by auto
          next 
            assume  i_in_pi:"i \<in> \<pi> x"
            hence   "\<pi> x = \<pi> i" using assms unfolding core_def valid_partition_def 
              by (smt (verit, ccfv_SIG) UnionI mem_Collect_eq rangeI subsetD)
            thus ?thesis using assms(5) i_in_pi by auto
          qed
        qed
      qed

lemma not_in_one_partition:
  fixes S \<pi>
  assumes "\<pi> \<in> core"
  and "\<exists>x\<in>S. \<not> S \<subseteq> \<pi> x"
  and "S \<subseteq> vertices"
shows "\<forall>x\<in>S.  \<not> S \<subseteq> \<pi> x "
proof
  fix x
  assume asm:"x \<in> S"
  from assms obtain y where y_def: "y \<in> S" "\<not> S \<subseteq> \<pi> y" by blast
  show "\<not> S \<subseteq> \<pi> x"
  proof (cases "y \<in> \<pi> x")
    case True
    hence "\<pi> x = \<pi> y" using asm assms(1) assms(3) unfolding core_def valid_partition_def
      by (smt (verit, ccfv_SIG) mem_Collect_eq subsetD y_def(1))
    then show ?thesis using y_def(2) by simp
    next
    case False
    then show ?thesis using y_def(1) by auto
  qed
qed





lemma blocking_coalition_cluster:
  fixes \<pi> x c                     
  assumes "x \<in> clusterNodes c"
  and "\<pi> \<in> core"
  and "\<forall>y \<in> clusterNodes c. val x (\<pi> x) \<ge> val y (\<pi> y)"
  and "\<forall> i\<in>\<pi> x. strict_pref_rel (clusterNodes c \<union> \<pi> x) i (\<pi> x)"
shows "blocking_coalition \<pi> (clusterNodes c \<union> \<pi> x)"
  unfolding blocking_coalition_def proof
  show "clusterNodes c \<union> \<pi> x \<noteq> {}" by (induct c rule: clusterNodes.induct) auto
next
  have  in_V:"clusterNodes c \<union> \<pi> x \<subseteq> vertices" using assms(2) assms(1) unfolding core_def valid_partition_def
    by blast
  moreover have "\<forall>i\<in>clusterNodes c \<union> \<pi> x. strict_pref_rel (clusterNodes c \<union> \<pi> x) i (\<pi> i)"
  proof
    fix i
    let ?S = "clusterNodes c \<union> \<pi> x"
    assume "i \<in> clusterNodes c \<union> \<pi> x"
    then show " strict_pref_rel (clusterNodes c \<union> \<pi> x) i (\<pi> i)"
    proof
      assume asm_i:"i \<in> clusterNodes c"
      hence t:"neighbors i \<union> {i} = neighbors x \<union> {x}"
              using same_cluster_neighbors[of i c x] assms(1) by  auto 
      hence "neighbors i = neighbors x \<union> {x} -{i} "
              using no_self_neighbor by auto
      hence "?S \<inter> neighbors i = (?S \<inter> (neighbors x \<union> {x})) -{i} " by auto
      moreover have "... = (?S \<inter> neighbors x) \<union> {x} -{i}" using assms(1) by fastforce
      ultimately have *: "?S \<inter> neighbors i  = (?S \<inter> neighbors x)  \<union> {x} -{i}" by simp
       have "card (?S \<inter> neighbors i) = card (?S \<inter> neighbors x) "
            proof(cases "i = x")
              case True
              then show ?thesis by auto
            next
              case False
              then have "i \<in> neighbors x" using t by auto
              hence "i \<in> (?S \<inter> neighbors x) \<union> {x}"   using asm_i by blast
              moreover have "x \<notin> (?S \<inter> neighbors x)" using no_self_neighbor by blast
              hence "card ((?S \<inter> neighbors x)  \<union> {x}) = card (?S \<inter> neighbors x) + 1"
                using finite_neighbors[of x] finite_subset[of "?S \<inter> neighbors x" "neighbors x"]
                by force
              ultimately show ?thesis using no_self_neighbor  "*" by auto
            qed
            hence "val_graph x ?S  = val_graph i ?S" 
              unfolding  val_graph_def by presburger
            moreover have finite_S: "finite ?S" 
              using in_V finite_subset finite_vertices by blast
            ultimately have "val i ?S = val x ?S" using val_graph_correct by auto
            moreover  have x'_pi:"x \<in> \<pi> x" using assms(2) assms(1) in_its_partition by blast
            hence "val x ?S > val x (\<pi> x)"  using assms(4) unfolding strict_pref_rel_def 
              by force
            moreover have "val x (\<pi> x)\<ge> val i (\<pi> i)" using assms(3) asm_i by blast
            ultimately show ?thesis unfolding strict_pref_rel_def by auto
          next 
            assume  i_in_pi:"i \<in> \<pi> x"
            hence   "\<pi> x = \<pi> i" using assms unfolding core_def valid_partition_def 
              by (smt (verit) Un_iff calculation mem_Collect_eq subsetD)
            thus ?thesis using assms(4) i_in_pi by fastforce
          qed
        qed
        ultimately show "clusterNodes c \<union> \<pi> x \<subseteq> \<Union> (range clusterNodes) \<and>
    (\<forall>i\<in>clusterNodes c \<union> \<pi> x. strict_pref_rel (clusterNodes c \<union> \<pi> x) i (\<pi> i))"
          by blast
      qed



lemma pi_in_neighbors:
  fixes \<pi> x
  assumes "\<pi> \<in> core"
  and "x \<in> clusterNodes c"
  and "val x ( \<pi> x) \<ge> (5::nat)/ (6::nat)"
  and "f (card (neighbors x)) < (5::nat)/ (6::nat)"
  shows "\<pi> x - {x} \<subseteq> neighbors x"
proof (rule ccontr)
  assume  asm_inc:" \<not> \<pi> x -{x} \<subseteq> neighbors x"
   hence "val x (\<pi> x) \<le> f (card (neighbors x))" using val_upper_bound assms
          by (smt (verit, ccfv_SIG)  numeral_Bit1 numeral_code(2) of_nat_numeral)
        thus  False using finite_neighbors[of x] assms  by auto
      qed


lemma cluster_in_pi:
  fixes x c l
  assumes "c = Cluster A l \<or> c = Cluster C l"
    and "x \<in> clusterNodes c"
    and "val x (\<pi> x) \<ge> (5::nat)/(6::nat)"
    and "\<pi> \<in> core"
  shows "\<exists>x'\<in> clusterNodes c . clusterNodes c \<subseteq> \<pi> x' \<and> (\<forall>x\<in>clusterNodes c. val x' (\<pi> x')\<ge> val x (\<pi> x))
    \<and> \<pi> x' - {x'} \<subseteq> neighbors x'
  "
proof -
    have "clusterNodes c \<noteq> {}" by (induct c rule: clusterNodes.induct) auto
     moreover have "finite (clusterNodes c)" using finite_clusterNodes by auto
      then obtain x' where asm:"x' \<in> clusterNodes c"
          "\<forall>x\<in>clusterNodes c. val x' (\<pi> x')\<ge> val x (\<pi> x)"
            "val x' ( \<pi> x') \<ge>  (5::nat)/ (6::nat)"
        using finite_sup[of "clusterNodes c" "\<lambda>x. val x (\<pi> x)"]
          assms(1) assms(2) assms(3) calculation  by (smt (verit, ccfv_SIG))
      then obtain n where "x' = Node c n" 
        by (metis Node.exhaust node_in_cluster)
      hence  card_neighbors:"card(neighbors x') = 7 \<or> card(neighbors x') = 9 "  using assms(1) card_neighbors_A card_neighbors_C
        asm(1)
        by (meson UnionI rangeI)
      hence "f (card(neighbors x')) < (5::nat) / (6::nat) " unfolding f_def  by auto
      hence pi_in_neighbors: "\<pi> x' - {x'} \<subseteq> neighbors x'"
        using pi_in_neighbors[of \<pi> x' c]  asm(1) asm(3) assms
        by fastforce 
      have "clusterNodes c \<subseteq> \<pi> x'"
      proof(rule ccontr)
        assume asm_contr:"\<not> clusterNodes c \<subseteq> \<pi> x'"
        let ?S = "clusterNodes c \<union> \<pi> x'"
        have pref_S_pi:"\<forall>i\<in>\<pi> x'. strict_pref_rel ?S i (\<pi> x')"
        proof
          fix i
          assume "i \<in> \<pi> x'"
          then show "strict_pref_rel ?S i (\<pi> x')"
          using  mono_in_neighbor'[of \<pi> x' c i] assms asm(1)  pi_in_neighbors
           asm_contr by fastforce 
         qed
      hence "blocking_coalition \<pi> ?S" using  blocking_coalition_cluster
        asm assms by blast
      thus False using assms(4) unfolding core_def in_core_def by auto
    qed
    thus ?thesis using asm pi_in_neighbors by blast
  qed

lemma card_val_upper_bound:
  fixes S n
  assumes "finite S"
  assumes "card (S \<inter> neighbors x) \<le> n"
  and "x \<in> S"
shows "val x S \<le> f' n"
proof -
  have "(S\<inter> neighbors x) \<subset> S"
    using assms no_self_neighbor by blast
  hence "card S > card (S\<inter> neighbors x)" using assms 
    by (meson psubset_card_mono)
  hence " card (S\<inter> neighbors x)/ card S \<le> f' (card (S\<inter> neighbors x))"
    unfolding f'_def 
    by (smt (verit, ccfv_SIG) divide_cancel_left frac_less2 nat_less_real_le of_nat_0_le_iff)
  moreover have "... \<le> f' n" using assms(2) mono_f' unfolding mono_def 
    using le_eq_less_or_eq by fastforce
  ultimately have  "val_graph x S \<le> f' n" unfolding val_graph_def by linarith
  thus ?thesis using assms(1) val_graph_correct by auto
qed

lemma card_val_upper_bound_strict:
  fixes S n
  assumes "finite S"
  assumes "card (S \<inter> neighbors x) < n"
  and "x \<in> S"
shows "val x S < f' n"
  using assms card_val_upper_bound 
  using mono_f' by fastforce

lemma card_val_lower_bound:
 fixes S n
  assumes "finite S"
  assumes " val x S \<ge> f' n"
  and "x \<in> S"
shows "card (S \<inter> neighbors x) \<ge> n"
  apply (rule ccontr)
  using card_val_upper_bound_strict assms by (meson linorder_not_le)

definition f_val :: "nat \<Rightarrow> nat \<Rightarrow> real" where 
"f_val n m \<equiv> n / (n+m)"

lemma f_val_rewrite:
  assumes "y>0"
shows "f_val x y = 1 - y/(x+y)"
  using assms  unfolding f_val_def
  apply (auto simp add:algebra_simps)
  by (metis add_divide_distrib add_gr_0 div_self less_numeral_extra(3) of_nat_0_less_iff of_nat_add)

lemma f_val_first:
  fixes x y z
  assumes "x \<le> y"
  and "z > 0"
  shows "f_val x z \<le> f_val y z"
  using assms  by (auto simp add: algebra_simps f_val_rewrite[of z] frac_le)  

lemma f_val_second:
  fixes x y z
  assumes "y\<ge> z"
  shows "f_val x y \<le> f_val x z"
  using assms unfolding f_val_def 
  by (smt (verit, ccfv_SIG) divide_cancel_left frac_le linorder_not_less of_nat_0_eq_iff of_nat_le_0_iff of_nat_less_iff)

lemma card_val_upper_bound':
  fixes S n m
  assumes "finite S"
  assumes "card (S \<inter> neighbors x) \<le> n"
  assumes "card (S - neighbors x) \<ge> m"
  assumes "m > 0"
  shows "val x S \<le> n/(n+m) "
proof -
  have "f_val (card (S \<inter> neighbors x)) (card (S - neighbors x)) \<le> f_val (card (S \<inter> neighbors x)) m"
    using f_val_second assms(3) by fast
  moreover have "f_val (card (S \<inter> neighbors x)) m \<le> f_val n m"
    using assms(4)  assms(2) f_val_first by presburger
  moreover have "val_graph x S = f_val (card (S \<inter> neighbors x)) (card (S - neighbors x))"
    unfolding val_graph_def f_val_def using assms(1)
    by (simp add: card_Diff_subset_Int card_mono of_nat_diff)
  ultimately show ?thesis using val_graph_correct
        assms(1)  f_val_def by auto
qed

lemma card_val_upper_bound'':
  fixes S S1 S2 n m x
  assumes "card S1 = n"
    and "card S2 = m"
  and "S2 \<noteq> {}"
  and "S \<inter> neighbors x \<subseteq> S1"
  and "S2 \<subseteq> S - neighbors x"
and "finite S"
and "finite S1"
shows "val x S \<le> n/(n+m) "
  using card_val_upper_bound'[of S x n m] assms card_mono[of S1 "S \<inter> neighbors x"] 
      finite_subset[of "S - neighbors x" S] card_mono[of "S - neighbors x" S2] 
  by (meson Diff_subset card_0_eq finite_subset gr0I)


lemma card_val_upper_bound_ineq:
  fixes S S1 S2 n m x
  assumes "card S1 \<le> n"
    and "card S2 = m"
  and "S2 \<noteq> {}"
  and "S \<inter> neighbors x \<subseteq> S1"
  and "S2 \<subseteq> S - neighbors x"
and "finite S"
and "finite S1"
shows "val x S \<le> n/(n+m) "
  using card_val_upper_bound'[of S x n m] assms card_mono[of S1 "S \<inter> neighbors x"] 
      finite_subset[of "S - neighbors x" S] card_mono[of "S - neighbors x" S2] 
  by (meson card_0_eq finite_Diff finite_subset gr0I le_trans)

lemma card_val_upper_bound''':
  fixes S S1 n m x
  assumes "card S1 = n"
    and "card S \<ge> m"
    and "m> 0"
  and "S \<inter> neighbors x \<subseteq> S1"
  and "S \<inter> neighbors x \<noteq> S"
and "finite S"
and "finite S1"
shows "val x S \<le> n/ m"
proof -
  have "card (S \<inter> neighbors x) \<le> n "  using assms card_mono by blast
  hence "val_graph x S \<le> n / card S" unfolding val_graph_def 
    by (smt (verit, best) assms(5) assms(6) card_0_eq card_mono finite_subset frac_le inf_le1 of_nat_le_0_iff of_nat_mono)
  moreover have  "... \<le> (n::nat) / (m::nat)" using assms(2) assms(3) 
    by (simp add: frac_le)
  ultimately show ?thesis using val_graph_correct assms(6) by auto
qed


lemma  cluster_core_min_val:
  fixes c1 c2 \<pi>
  assumes "clusterEdge c1 c2"
  and "\<pi> \<in> core" 
  and "c1 \<noteq> c2" 
  shows "\<exists>x \<in> clusterNodes c1 \<union> clusterNodes c2. val x (\<pi> x)\<ge> f' (clusterCard c1 + clusterCard c2 - 1)"
proof - 
  have "clusterEdge c2 c1" using assms(1) by (induct c2 c1 rule:clusterEdge.induct) auto 
  hence  * :"c1 \<in> neighboring_clusters c2" "c2 \<in> neighboring_clusters c1" using assms(1) neighboring_clusters_correct by auto
  have t:"\<forall>x \<in>  clusterNodes c1 \<union> clusterNodes c2. val x (clusterNodes c1 \<union> clusterNodes c2) = f' (clusterCard c1 + clusterCard c2 - 1)"
  proof
    fix x
    assume asm: "x \<in> clusterNodes c1 \<union> clusterNodes c2"
    hence "clusterNodes c1 \<union> clusterNodes c2 -{x} \<subseteq> neighbors x" using "*" in_neighboring neighbors_correct_set by auto
    hence "(clusterNodes c1 \<union> clusterNodes c2)\<inter> neighbors x = (clusterNodes c1 \<union> clusterNodes c2) - {x}" using no_self_neighbor by blast
    moreover have  "card ((clusterNodes c1 \<union> clusterNodes c2) - {x}) = card (clusterNodes c1 \<union> clusterNodes c2) - 1 "
      using asm finite_clusterNodes by force
    moreover have "card(clusterNodes c1 \<union> clusterNodes c2) = clusterCard c1 + clusterCard c2" using clusterCard_correct finite_clusterNodes 
      by (simp add: assms(3) card_Un_disjoint clusterNodes_inter_empty)
    ultimately have "val_graph x (clusterNodes c1 \<union> clusterNodes c2) = f'( (clusterCard c1 + clusterCard c2) -1)"
      unfolding f'_def val_graph_def by force
    thus "val x (clusterNodes c1 \<union> clusterNodes c2) =
     f' (clusterCard c1 + clusterCard c2 - 1)" using finite_clusterNodes 
      using val_graph_correct by force
  qed
  show ?thesis 
  proof (rule ccontr) 
    assume asm: "\<not> (\<exists>x\<in>clusterNodes c1 \<union> clusterNodes c2.
           f' (clusterCard c1 + clusterCard c2 - 1) \<le> val x (\<pi> x))"
    have "blocking_coalition \<pi> (clusterNodes c1 \<union> clusterNodes c2)"
      unfolding blocking_coalition_def strict_pref_rel_def
    proof
      show "clusterNodes c1 \<union> clusterNodes c2 \<noteq> {}" by (induct c1 c2 rule:clusterEdge.induct) auto
    next
      show "clusterNodes c1 \<union> clusterNodes c2 \<subseteq> \<Union> (range clusterNodes) \<and>
    (\<forall>i\<in>clusterNodes c1 \<union> clusterNodes c2.
        val i (\<pi> i) \<le> val i (clusterNodes c1 \<union> clusterNodes c2) \<and>
        \<not> val i (clusterNodes c1 \<union> clusterNodes c2) \<le> val i (\<pi> i))"
        using asm t 
        by (smt (verit, ccfv_SIG) UNIV_I UN_upper Un_least)
    qed  
    thus False using assms(2) unfolding core_def in_core_def by auto
  qed
qed
lemma not_in_many_clusters'[simp]:
  fixes x c1 c2
  assumes "x \<in> clusterNodes c1" " x \<in> clusterNodes c2"
  shows "c1 = c2"
 using assms  clusterNodes_inter_empty by blast 
    
lemma  neighbors_intersection:
  fixes x y cx cy
  assumes "x \<in> clusterNodes cx"
  and "y \<in> clusterNodes cy"
shows "neighbors x \<inter> neighbors y = (\<Union> (clusterNodes `(neighboring_clusters cx \<inter> neighboring_clusters cy))) - {x,y}"
  unfolding  neighbors_correct_set[OF assms(2)] neighbors_correct_set[OF assms(1)]
  using not_in_many_clusters' by blast

lemma mono_inter: "S \<subseteq> T \<Longrightarrow> S \<inter> P \<subseteq> T \<inter> P"
  by auto

lemma pred2_diff[simp]:
"pred (pred l) \<noteq> l"
  by (cases l) auto
lemma suc2_diff[simp]:
"Suc (Suc l) \<noteq> l"
  by (cases l) auto


lemma neighbor_check:
  fixes x y c1 c2
  assumes "x \<in> clusterNodes c1"
  and "y \<in> clusterNodes c2 "
shows "x \<in> neighbors y = (clusterEdge c2 c1 \<and> x\<noteq> y)"
proof -
  obtain nx ny where "x = Node c1 nx" "y = Node c2 ny" 
    by (metis assms(1) assms(2) example_2.Node.exhaust node_in_cluster)
  thus ?thesis unfolding  neighbors_def using assms by auto
qed

lemma no_triangle_cluster:
  fixes c1 c2 c
  assumes "clusterEdge c1 c2"
  and "c1 \<noteq> c2"
  and "c \<in> neighboring_clusters c1 \<inter> neighboring_clusters c2"
shows "c = c1 \<or> c = c2"
  using assms apply (induct c1 c2 rule: clusterEdge.induct)
  using  suc2_diff suc_diff pred2_diff by (auto,metis+)

corollary no_triangle_cluster_plus:
  fixes c1 c2
  assumes "clusterEdge c2 c1"
  and "c2 \<noteq> c1"
shows "neighboring_clusters c1 \<inter> neighboring_clusters c2 = {c1,c2}"
  using assms apply (induct c1 c2 rule: clusterEdge.induct)
  using  suc2_diff suc_diff pred2_diff by (auto,metis+)

lemma  edge_means_neighboring:
  fixes c1 c2
  assumes "clusterEdge c1 c2"
  shows "c1 \<in> neighboring_clusters c2" "c2 \<in> neighboring_clusters c1"
  using assms  by (induct c1 c2 rule:clusterEdge.induct)  (auto simp add: pred_suc)

lemma val_cluster:
  fixes x c
  assumes "x \<in> clusterNodes c"
  shows "val x (clusterNodes c) = (clusterCard c -1) / clusterCard c"
proof -
  have "clusterNodes c \<inter> neighbors x = clusterNodes c - {x}"
    by (smt (verit, best) Diff_eq_empty_iff Diff_insert0 Int_insert_left_if0 Un_Diff_cancel Un_Int_eq(4) Un_commute assms cluster_is_neighbors_neighbor insert_Diff1 insert_is_Un mk_disjoint_insert neighbors_correct_set sup_bot.right_neutral)
  hence "val_graph x (clusterNodes c) = (clusterCard c -1) / clusterCard c  "
    using clusterCard_correct assms unfolding val_graph_def by auto
  thus ?thesis using val_graph_correct finite_clusterNodes by auto
qed

lemma k1_k5_partition:
  fixes k e c l
  assumes "c = Cluster B l \<or> c = Cluster B (pred l)"
  and "k \<in> clusterNodes c"
  and "e \<in> clusterNodes (Cluster A l)"
  and "k \<notin> \<pi> e"
  and "val k (\<pi> k) \<ge> (4::nat)/ (5::nat)"
  and "\<pi> \<in> core"
shows "\<pi> k - {k} \<subseteq> neighbors k"
proof -
  have "e \<notin> \<pi> k" using assms(5) 
    by (smt (verit, ccfv_threshold) UnionI assms(2) 
        assms(3) assms(4) assms(6) core_def mem_Collect_eq rangeI valid_partition_def)
  hence pi_neighbors_e: "\<pi> k \<inter> neighbors k \<subseteq> neighbors k - {e}" by blast
  moreover have "e \<in> neighbors k" using assms(1) assms(2) assms(3) neighbors_correct_set 
    by (metis (no_types, lifting) assms(4) assms(6) clusterEdge.simps(4) example_2.in_its_partition neighbor_check suc_pred)
  hence  card_k_e:"card(neighbors k - {e}) = 9" using assms(1) assms(2) card_neighbors_B' finite_clusterNodes 
    using DiffD2 Diff_empty by auto
  ultimately have card_nom: "card (\<pi> k \<inter> neighbors k) \<le> 9" 
    by (metis (no_types, lifting) card_mono finite_Diff finite_neighbors)
  show ?thesis 
  proof(rule ccontr)
    assume  " \<not> \<pi> k - {k} \<subseteq> neighbors k"
    hence asm: "\<pi> k - {k} - neighbors k \<noteq> {}" by blast
    hence "card (\<pi> k - {k} - neighbors k) \<ge>2 \<or> card (\<pi> k - {k} - neighbors k) = 1"
      using finite_pi' assms(6) assms(2) 
      by (metis (no_types, lifting) BitM.simps(1) One_nat_def Suc_eq_numeral Suc_leI card_gt_0_iff finite_Diff le_eq_less_or_eq numeral_One pred_numeral_simps(2))
    thus False 
    proof
      assume "card (\<pi> k - {k} - neighbors k) \<ge>2"
      hence "card (\<pi> k -neighbors k) \<ge> 3" 
        by (smt (verit, ccfv_threshold) BitM.simps(1) Diff_cancel Diff_insert Diff_insert2 One_nat_def Suc_diff_eq_diff_pred asm assms(2) assms(6) card_Diff_insert card_gt_0_iff diff_is_0_eq example_2.in_its_partition finite_Diff finite_pi' insert_Diff_single no_self_neighbor numeral_3_eq_3 numeral_nat(2) numerals(1))
      hence "val k (\<pi> k) \<le> 9/ 12" using card_nom 
        by (smt (verit, ccfv_threshold) assms(2) assms(6) card_val_upper_bound' finite_pi' numeral_3_eq_3 numeral_Bit0 numeral_code(3) numeral_plus_one of_nat_numeral semiring_norm(2) zero_less_Suc) 
      thus False using assms(5) by linarith
    next
      assume pi_minus_neighbors: "card (\<pi> k - {k} - neighbors k) = 1"
      hence card_denom:"card (\<pi> k - neighbors k) = 2"
        using in_its_partition[of \<pi> k c] assms(6) assms(2)  no_self_neighbor[of k] 
        by (smt (verit, best) Diff_insert2 Nat.add_diff_assoc card_Diff_insert diff_add_inverse diff_le_self one_add_one)
      have "card(\<pi> k \<inter> neighbors k)\<le> 7 \<or> card (\<pi> k \<inter>neighbors k) \<ge> 8" 
        by linarith
      thus False 
      proof
        assume "card (\<pi> k \<inter> neighbors k) \<le> 7"
        then have "val k (\<pi> k) \<le> 7/9" using card_denom card_val_upper_bound'[of "\<pi> k" k 7 2]
          finite_pi'[of \<pi> k c] assms(6) assms(2) by auto
        thus False using assms(5) by auto
      next
        let ?P = "\<lambda>c' . clusterNodes c' \<subseteq> \<pi> k \<and> clusterEdge c c' "
        assume asm_8: "card (\<pi> k \<inter> neighbors k) \<ge> 8"
        hence "card (\<pi> k \<inter> neighbors k) = 8 \<or> card (\<pi> k \<inter> neighbors k) = 9"
          using card_nom by linarith
        then have "\<exists>l. ?P (Cluster A l)  \<or> ?P (Cluster C l) " 
        proof
          assume asm_card:"card (\<pi> k \<inter> neighbors k) = 8"
          then obtain m where m_def: "m \<in> neighbors k -{e}" "m \<notin> \<pi> k \<inter> neighbors k "
            using card_k_e pi_neighbors_e 
            by (smt (verit, best) card_mono finite_neighbors finite_subset inf_le2 le_simps(2) linorder_not_less numeral_eq_Suc pred_numeral_simps(3) subsetI)
          hence card_':"card (neighbors k -{e,m}) = 8" using pi_neighbors_e 
            by (metis (no_types, lifting) Diff_insert2 card_Diff_singleton card_k_e diff_add_inverse2 numeral_Bit1 numeral_code(2))
          have inter_eq:"\<pi> k \<inter> neighbors k = neighbors k -{e,m} "
            apply (rule card_subset_eq[of " neighbors k - {e,m}" "\<pi> k \<inter> neighbors k" ])
            using  card_subset_eq[of " neighbors k - {e,m}" "\<pi> k \<inter> neighbors k" ] finite_neighbors[of k] finite_subset[of  "neighbors k - {e,m}" "neighbors k"] apply blast
            using  pi_neighbors_e m_def apply blast
            using card_' asm_card by presburger
          obtain la lc where l'_def: "Cluster A la \<in> neighboring_clusters c" "Cluster C lc \<in> neighboring_clusters c" 
                "la \<noteq> l"
            using assms(1)  suc_pred pred_diff suc_diff by auto
          hence "e \<notin> clusterNodes(Cluster A la)"
            "e \<notin> clusterNodes(Cluster C lc)"
            using  clusterNodes_inter_empty assms(3) by auto
          moreover have "k \<notin> clusterNodes (Cluster A la )" "k \<notin> clusterNodes (Cluster C lc)"
            using assms(2) assms(1)  clusterNodes_inter_empty  by auto
          ultimately have clust_in_neigh:"clusterNodes (Cluster A la ) \<subseteq> neighbors k -{e}"
            "clusterNodes (Cluster C lc) \<subseteq> neighbors k - {e}"
            using neighbors_correct_set[of k c]  assms(2) l'_def by blast+
          have "clusterNodes (Cluster A la ) \<subseteq> neighbors k -{e,m} \<or> clusterNodes (Cluster C lc ) \<subseteq> neighbors k -{e,m}"
          proof (cases "m \<in>clusterNodes (Cluster A la )")
            case True
            hence "m \<notin> clusterNodes (Cluster C lc)" using clusterNodes_inter_empty by auto
            hence " clusterNodes (Cluster C lc ) \<subseteq> neighbors k -{e,m}" using clust_in_neigh(2) by blast
            then show ?thesis by blast
          next
            case False
            hence " clusterNodes (Cluster A la ) \<subseteq> neighbors k -{e,m}" using clust_in_neigh(1) by blast
            then show ?thesis by blast
          qed
          thus ?thesis  using inter_eq l'_def(1) l'_def(2) neighboring_clusters_correct by auto  
        next
          assume "card (\<pi> k \<inter> neighbors k) = 9"
          hence inter_eq: "\<pi> k \<inter> neighbors k = neighbors k - {e}" using card_subset_eq  
            by (metis (no_types, lifting) card_k_e finite.emptyI finite.insertI finite_Diff2 finite_neighbors pi_neighbors_e)
          obtain lc where l'_def: "Cluster C lc \<in> neighboring_clusters c" using assms(1) by auto
          moreover have "k \<notin> clusterNodes (Cluster C lc)" using clusterNodes_inter_empty 
            using assms(1) assms(2) by blast
          ultimately have "clusterNodes( Cluster C lc) \<subseteq> neighbors k" using neighbors_correct_set
                  assms(2) by blast
          moreover have "e \<notin> clusterNodes( Cluster C lc) " using clusterNodes_inter_empty assms(3)
            by auto
          ultimately have "clusterNodes( Cluster C lc) \<subseteq> \<pi> k" using inter_eq by auto
          thus ?thesis using l'_def neighboring_clusters_correct by auto
        qed
        then obtain c' l' where c'_def: "c' = Cluster A l' \<or> c' = Cluster C l'" "clusterNodes c' \<subseteq> \<pi> k"
          "clusterEdge c c'" by blast
        have "\<forall>x \<in> clusterNodes c'. val x (\<pi> x) \<le> 5/ 10 "
        proof
          fix x
          assume asm_c:"x \<in> clusterNodes c'"
          hence x_def:"x \<in> \<pi> k" using c'_def(2) by blast
          hence "\<pi> x = \<pi> k" using assms(6) assms(2) asm_c unfolding core_def valid_partition_def
            by blast
          obtain y where y_def: "\<pi> k -{k} - neighbors k = {y}" using pi_minus_neighbors is_singleton_altdef
            is_singleton_def by meson
          have "val x (\<pi> k) \<le> real 5/  real 10"
            thm  card_val_upper_bound'''[of "clusterNodes c \<union> clusterNodes c' \<union> {y} - {x}" 5 10 "\<pi> k" x ]
          proof (rule card_val_upper_bound'''[of "clusterNodes c \<union> clusterNodes c' \<union> {y} - {x}" 5 10 "\<pi> k" x ], goal_cases)
            case 1
            have "card(clusterNodes c) = 2" using assms(1) clusterCard_correct by auto
            moreover have "card(clusterNodes c') = 3" using c'_def(1) clusterCard_correct by auto
            moreover have  y_not_k_neighbor:"y \<notin> neighbors k " using y_def by auto
            hence "\<forall>c'' \<in> neighboring_clusters c. y \<notin> clusterNodes c''" using neighbors_correct_set
              y_def assms(2) by blast
            hence "y \<notin> clusterNodes c"  "y \<notin> clusterNodes c'" 
              using in_neighboring  by (auto simp add: c'_def(3) neighboring_clusters_correct) 
            moreover have "c \<noteq> c'" 
              using assms(1) c'_def(1) by blast
            ultimately show ?case using asm_c clusterNodes_inter_empty[of c c'] finite_clusterNodes[of c] finite_clusterNodes[of c']
                    card_Un_disjoint[of "clusterNodes c" "clusterNodes c'"] by auto
          next
            case 2
            have "\<pi> k - neighbors k = {y,k}" using y_def no_self_neighbor[of k] 
              using Diff_insert assms(2) assms(6) example_2.in_its_partition insert_Diff by auto
            hence "card (\<pi> k - neighbors k) = 2" using card_denom by blast 
            then show ?case using asm_8 finite_pi' assms(6) assms(2) finite_subset[of _ "\<pi> k"] 
                  card_Un_disjoint[of "\<pi> k \<inter> neighbors k" "\<pi> k - neighbors k"] 
              by (smt (verit, best) Int_Diff_Un Int_Diff_disjoint finite_Diff2 finite_Int finite_neighbors nat_le_real_less numeral_Bit0 numeral_le_real_of_nat_iff numeral_plus_numeral of_nat_add semiring_norm(3))
          next
            case 3
            then show ?case by auto
          next
            case 4
            have "neighbors k \<inter> neighbors x \<subseteq> \<Union> (clusterNodes ` (neighboring_clusters c \<inter> neighboring_clusters c'))"
              using asm_c assms(2) neighbors_intersection by auto
            moreover have "c \<noteq> c'"  using assms(1) c'_def(1) by blast
            hence "neighboring_clusters c \<inter> neighboring_clusters c' = {c ,c'}" 
              using  no_triangle_cluster[of c c'] c'_def(3) edge_means_neighboring in_neighboring  
              by auto
            ultimately have "neighbors k \<inter> neighbors x \<subseteq> clusterNodes c \<union> clusterNodes c'"
              by auto
            hence "neighbors k \<inter> neighbors x \<subseteq> clusterNodes c \<union> clusterNodes c' -{x}" using no_self_neighbor by auto
            hence "\<pi> k \<inter> neighbors x \<inter> neighbors k \<subseteq> clusterNodes c \<union> clusterNodes c' - {x}"
              by auto
            moreover have " (\<pi> k \<inter> neighbors x) - neighbors k \<subseteq> {y,k}" using y_def by auto
            ultimately show ?case 
              by (smt (verit, ccfv_threshold) Diff_eq_empty_iff Diff_iff Int_iff UnCI asm_c assms(2) insertE neighbors_correct_set subsetI y_def)
          next
            case 5
            then show ?case using x_def no_self_neighbor by fastforce
          next
            case 6
            then show ?case using finite_pi' assms(6) assms(2) by blast
          next
            case 7
            then show ?case using finite_clusterNodes by auto
          qed
          moreover have "\<pi> x = \<pi> k" using x_def asm_c
             assms(2)     assms(6) unfolding core_def valid_partition_def 
            by blast
          ultimately show "val x (\<pi> x) \<le> 5 / 10" by auto
        qed
        moreover have "\<forall>x \<in> clusterNodes c'. val x (clusterNodes c') = 2/3"
          using val_cluster using c'_def(1) by auto
        ultimately have "\<forall>x \<in> clusterNodes c'. strict_pref_rel (clusterNodes c') x (\<pi> x)"
          unfolding strict_pref_rel_def by force
        hence "blocking_coalition \<pi> (clusterNodes c')"
          unfolding blocking_coalition_def using c'_def(1) by auto
        thus False using assms(6) unfolding core_def in_core_def by auto
      qed
    qed
  qed
qed

lemma blocking_coalition_if_connected:
  fixes j c X
  assumes "j \<in> clusterNodes c"
  and "\<forall>x\<in>clusterNodes c. val j (\<pi> j) \<ge> val x ( \<pi> x)"
  and " X \<subseteq> clusterNodes c"
  and "X \<noteq> {}"
  and " \<not> X \<subseteq> \<pi> j"
  and "\<pi> j - {j} \<subseteq> neighbors j"
  and "\<pi> \<in> core"
shows "blocking_coalition \<pi> (X \<union> \<pi> j) "
proof -
  have "\<forall>i \<in>\<pi> j. strict_pref_rel (X \<union> \<pi> j) i (\<pi> j)"
    using  mono_in_neighbor_general[of \<pi> j c X ]  assms by auto
  thus "blocking_coalition \<pi> (X \<union> \<pi> j)"
    using blocking_coalition_cluster_general[of j c X \<pi>] assms by auto
qed

lemma partition_relation:
  fixes a b \<pi>
  assumes "\<pi> \<in> core"
  and "a \<in> clusterNodes c"
  and "b \<in> clusterNodes c'"
shows "(if (a \<in> \<pi> b) then \<pi> a = \<pi> b else \<pi> a \<inter> \<pi> b ={} )"
  using assms 
  by (smt (verit, del_insts) UnionI core_def disjoint_iff mem_Collect_eq rangeI subset_eq valid_partition_def)

lemma card_one_diff:
  fixes S T
  assumes "S \<subseteq> T"
  and "card T = card S + 1"
shows "\<exists>x. T - S = {x}"
proof -
  have "card (T - S) = 1" using assms 
    by (metis One_nat_def add_diff_cancel_left' bot_nat_0.extremum_unique card.infinite card_Diff_subset card_gt_0_iff finite_subset le_add2 zero_less_Suc)
  thus ?thesis 
    by (meson card_1_singletonE)
qed

lemma cluster_neighbor_check:
  fixes c x cx
  assumes "x \<in> clusterNodes cx"
  and "clusterEdge cx c"
  and "c \<noteq> cx"
  shows "clusterNodes c \<subseteq> neighbors x"
proof -
  have "x \<notin> clusterNodes c" using assms(1) assms(3) clusterNodes_inter_empty by blast
  moreover have "c \<in> neighboring_clusters cx" using assms(2) neighboring_clusters_correct 
    by blast
  ultimately show ?thesis using neighbors_correct_set assms(1) by blast
qed

lemma cluster_not_neighbor_check:
  fixes c x cx
  assumes "x \<in> clusterNodes cx"
  and " \<not> clusterEdge cx c"
  shows "clusterNodes c \<inter> neighbors x = {}"
proof -
 have "c \<notin> neighboring_clusters cx" using assms(2) neighboring_clusters_correct 
    by blast
  then show ?thesis using neighbors_correct_set assms(1) 
    using assms(2) neighbor_check by fastforce
qed

lemma A_superplayer_aux:
  assumes "\<pi> \<in> core"
  and "\<forall>x \<in> vertices.  \<not> clusterNodes (Cluster A l) \<subseteq> \<pi> x"
shows "(\<exists>x'\<in> clusterNodes (Cluster C l). \<exists>X \<subseteq> clusterNodes(Cluster A l) . \<exists>b \<in> clusterNodes (Cluster  B (pred (pred l))).
         \<pi> x' = clusterNodes (Cluster C l) \<union> X \<union> {b} 
        \<and> card X = 2 ) \<and>
(\<exists>k1\<in> clusterNodes (Cluster B l). val k1 (\<pi> k1) \<ge> (4::nat)/(5::nat) \<and> \<pi> k1 - {k1} \<subseteq> neighbors k1)\<and>
(\<exists>k5\<in> clusterNodes (Cluster B (pred l)). val k5 (\<pi> k5) \<ge> (4::nat)/(5::nat) \<and> \<pi> k5- {k5} \<subseteq> neighbors k5)"
proof  -  
    obtain x where x_def:"x\<in>clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l)"
            "val x (\<pi> x) \<ge> (5::nat)/(6::nat)"      
    using cluster_core_min_val[of "Cluster A l" "Cluster C l"] assms(1) unfolding f'_def
    by auto
    hence x_cases:"x \<in> clusterNodes (Cluster A l) \<or>x \<in> clusterNodes (Cluster C l)"
           by auto
    thus ?thesis
    proof
      assume asm_x: "x \<in> clusterNodes (Cluster A l)"
      hence "\<exists>x'\<in> clusterNodes (Cluster A l). clusterNodes (Cluster A l) \<subseteq> \<pi> x'"
        using  cluster_in_pi[of "Cluster A l" l x \<pi>]  assms x_def(2) by blast
      hence  False using assms   unfolding core_def in_core_def by blast
      thus ?thesis by auto
    next
      assume asm_x:"x \<in> clusterNodes (Cluster C l)"
      then obtain x' where  x'_def: "x'\<in> clusterNodes (Cluster C l)" 
          " clusterNodes (Cluster C l) \<subseteq> \<pi> x'" "(\<forall>x\<in>clusterNodes (Cluster C l). val x' (\<pi> x')\<ge> val x (\<pi> x))"
          "\<pi> x' - {x'} \<subseteq> neighbors x'"
        using  cluster_in_pi[of "Cluster C l" l x \<pi>]  assms x_def(2) by blast
      then obtain n where n_def: "x' = Node (Cluster C l) n"   using clusterNodes.simps(3) by blast
      have "\<pi> x' \<inter> clusterNodes(Cluster A l) \<noteq> {}"
      proof (rule ccontr)
        assume " \<not> \<pi> x' \<inter> clusterNodes (Cluster A l) \<noteq> {} "
        hence  "\<pi> x' \<inter> neighbors x' \<subseteq> neighbors x' -  clusterNodes (Cluster A l)" by blast
        moreover have "x' \<notin> clusterNodes (Cluster A l) " using n_def by auto
        hence  "clusterNodes (Cluster A l) \<subseteq> neighbors x'" using neighbors_correct n_def
          x'_def(1) by fastforce
        hence "card (neighbors x' -  clusterNodes (Cluster A l)) = card( neighbors x') - card( clusterNodes (Cluster A l))"
          using finite_neighbors  by (meson card_Diff_subset finite_clusterNodes)
        moreover have  "... =  card( neighbors x') - clusterCard (Cluster A l)" using  clusterCard_correct  by presburger
        moreover have  "... = 4" using card_neighbors_C  x'_def(1) n_def  by fastforce
        ultimately have "card (\<pi> x' \<inter> neighbors x') \<le> (4::nat) "   by (metis (mono_tags, lifting) card_mono finite_Diff finite_neighbors)
        hence "val x' (\<pi> x') \<le> (4::nat)/(5::nat)" using card_val_upper_bound finite_subset assms core_def valid_partition_def
          by (smt (verit, best) f'_def finite_pi' numeral_Bit1 numeral_code(2) of_nat_numeral subsetD x'_def(1) x'_def(2))
        moreover have "val x' (\<pi> x') \<ge> (5::nat)/(6::nat)" using asm_x  x_def(2) x'_def(3) by fastforce
        ultimately show False by linarith
      qed
      then obtain X where  X_def :"X = \<pi> x' \<inter> clusterNodes (Cluster A l)" "X \<noteq> {}" "X \<subset> clusterNodes (Cluster A l)"
        using assms(2) by (metis UnionI inf_le1 inf_le2 psubsetI rangeI x'_def(1))
      have pi_B_pred_pred:" \<pi> x' \<inter> clusterNodes(Cluster B (pred (pred l))) \<noteq> {}"
      proof  (rule ccontr)
        assume " \<not> \<pi> x' \<inter> clusterNodes (Cluster B (pred  (pred l))) \<noteq> {} "
        hence  "\<pi> x' \<inter> neighbors x' \<subseteq> neighbors x' -  clusterNodes (Cluster B (pred  (pred l)))" by auto
        moreover have " \<not> clusterNodes (Cluster A l) \<subseteq> \<pi> x' " using assms(2) x'_def(1) by blast
        moreover have "x' \<notin>  clusterNodes (Cluster A l) "  using x'_def(1) by auto
        hence  "clusterNodes (Cluster A l) \<subseteq> neighbors x' "  using neighbors_correct x'_def(1) n_def 
          by fastforce
        hence "clusterNodes (Cluster A l) \<subseteq> neighbors x' - clusterNodes (Cluster B (pred (pred l)))"
          using clusterNodes_inter_empty[of "Cluster A l"  "Cluster B (pred (pred l))"] by auto
        ultimately have  "\<pi> x' \<inter> neighbors x' \<subset>  neighbors x' -  clusterNodes (Cluster B (pred  (pred l)))"
          by blast
        moreover have "x' \<notin> clusterNodes (Cluster B (pred  (pred l))) " using n_def by auto
        hence  "clusterNodes (Cluster B (pred  (pred l))) \<subseteq> neighbors x'" using neighbors_correct n_def
          x'_def(1) by fastforce
        hence "card (neighbors x' -  clusterNodes  (Cluster B (pred  (pred l)))) = card( neighbors x') - card( clusterNodes  (Cluster B (pred  (pred l))))"
          using finite_neighbors  by (meson card_Diff_subset finite_clusterNodes)
        moreover have  "... =  card( neighbors x') - clusterCard (Cluster B (pred  (pred l)))" using  clusterCard_correct  by presburger
        moreover have  "... = 5" using card_neighbors_C  x'_def(1) n_def  by fastforce
         ultimately have "card (\<pi> x' \<inter> neighbors x') \<le> (4::nat) "  
           by (metis (mono_tags, lifting) Sup_upper finite_Diff2 finite_neighbors finite_vertices infinite_super le_simps(2) numeral_eq_Suc pred_numeral_simps(3) psubset_card_mono rangeI)
        hence "val x' (\<pi> x') \<le> (4::nat)/(5::nat)" using card_val_upper_bound finite_subset assms core_def valid_partition_def
          by (smt (verit, best) f'_def finite_pi' numeral_Bit1 numeral_code(2) of_nat_numeral subsetD x'_def(1) x'_def(2))
        moreover have "val x' (\<pi> x') \<ge> (5::nat)/(6::nat)" using asm_x  x_def(2) x'_def(3) by fastforce
        ultimately show False by auto
      qed
      obtain k1 where k1_def: "k1 \<in> clusterNodes (Cluster A l) \<union> clusterNodes (Cluster B l)"
                  "val k1 (\<pi> k1)\<ge> (4::nat)/(5::nat)" using cluster_core_min_val[of "Cluster A l" "Cluster B l" \<pi>] unfolding f'_def
        using assms semiring_norm(3) by auto
       obtain k5 where k5_def: "k5 \<in> clusterNodes (Cluster A l) \<union> clusterNodes (Cluster B (pred l))"
                  "val k5 (\<pi> k5)\<ge> (4::nat)/(5::nat)" using cluster_core_min_val[of "Cluster A l" "Cluster B (pred l)" \<pi>] unfolding f'_def 
         using assms semiring_norm(3) pred_suc suc_pred by auto
       have "\<forall>j\<in> clusterNodes (Cluster A l). val j (\<pi> j) < (4::nat)/(5::nat) "
       proof
         fix j0
         assume asm_j': "j0 \<in> clusterNodes (Cluster A l)"
         then obtain j where asm_j: "j \<in> clusterNodes (Cluster A l)" "\<forall>j' \<in> clusterNodes (Cluster A l).
                val j (\<pi> j) \<ge> val j' (\<pi> j')" using finite_clusterNodes finite_sup[of "clusterNodes(Cluster A l)" "\<lambda>x. val x (\<pi> x)"]
           by blast
         have " val j (\<pi> j) < (4::nat)/(5::nat)"
         proof(cases "j \<in> X")
           case True
let ?S = "(\<Union> (clusterNodes ` (neighboring_clusters  (Cluster C l) \<inter>  neighboring_clusters  (Cluster A l) )))"
         obtain a where a_def:"a \<noteq> j" "a \<noteq> x'" "a \<in> clusterNodes (Cluster A l)" "a \<notin> \<pi> x'" 
           by (smt (verit, ccfv_threshold) Int_iff True UNIV_I UN_iff X_def(1) assms(2) subsetD subsetI x'_def(1) x'_def(2))
        moreover from asm_j have  j_cluster:"j \<in> clusterNodes (Cluster A l)" using X_def by blast
         hence "\<pi> x' \<subseteq> neighbors x' \<union> {x'}" 
           using Diff_subset_conv Un_commute x'_def(4)  by auto
         moreover have x'_j_neighbors:"x' \<in> neighbors j" using neighbors_correct_set[of j "Cluster A l"] j_cluster x'_def(1) 
           by auto
         ultimately have "\<pi> x' \<inter> neighbors j \<subseteq> (?S - {x',j, a}) \<union> {x'}"
           using neighbors_intersection[of x' "Cluster C l" j "Cluster A l"] mono_inter[of "\<pi> x'" " neighbors x' \<union> {x'}" "neighbors j"]
           using j_cluster x'_def(1) by blast
         moreover have "neighboring_clusters  (Cluster C l) \<inter>  neighboring_clusters  (Cluster A l) = {Cluster A l, Cluster C l}"
           using pred_diff pred2_diff by auto
         hence * :"card ?S = clusterCard (Cluster A l) + clusterCard ( Cluster C l) "
           by auto
         have  x'_in:"x' \<in> ?S" "j \<in> ?S" using x'_def(1) j_cluster  by fastforce+
         have ***:"x' \<noteq> j" using j_cluster x'_def(1) by auto
         have **: "finite ?S" by auto
         have "card(?S - {x',j}) = clusterCard (Cluster A l) + clusterCard ( Cluster C l) -2 "
           using * ** x'_in  *** 
           by (metis card_Diff_insert card_Diff_singleton diff_diff_left empty_iff insert_iff nat_1_add_1)
         hence "card(?S - {x',j}-{a}) = clusterCard (Cluster A l) + clusterCard ( Cluster C l) -3"
           using a_def **
           by (metis (no_types, lifting) BitM.simps(1) Diff_insert One_nat_def UN_I \<open>neighboring_clusters (Cluster C l) \<inter> neighboring_clusters (Cluster A l) = {Cluster A l, Cluster C l}\<close> card_Diff_insert diff_Suc_eq_diff_pred insert_iff numeral_3_eq_3 numeral_nat(2) numerals(1) singleton_iff)
         hence "card(?S - {x',j}-{a} \<union> {x'}) = clusterCard (Cluster A l) + clusterCard ( Cluster C l) -2"
           using ** by auto
         moreover have "finite (?S - {x',j} -{a} \<union> {x'})" by auto
         moreover have jth:"j \<in> \<pi> x' " "j \<notin> neighbors j" using asm_j X_def(1) no_self_neighbor True by auto
         moreover obtain j' where j'_def: "j' \<in> clusterNodes (Cluster B (pred (pred l)))"
              "j' \<noteq> j" "j' \<in> \<pi> x'" using pi_B_pred_pred j_cluster by auto
         have "Cluster B (pred (pred l)) \<notin> neighboring_clusters (Cluster A l)" by (auto simp add: pred2_diff pred_diff)
         hence th:"j' \<in> \<pi> x'" "j' \<notin> neighbors j"  using  j_cluster neighbors_correct_set[of j "Cluster A l"]
           using j'_def(1) j'_def(3) by fastforce +
         have "val j (\<pi> x') \<le> real 4 / (real 4 + real 2)"
           apply (rule card_val_upper_bound''[of "?S - {x',j}-{a} \<union> {x'}" "4::nat" "{j,j'}" "2::nat" "\<pi> x'" j ])
           using calculation(2) apply auto[1]
           using card_2_iff j'_def(2) apply blast
               apply blast
           using calculation(1) apply blast
           using calculation(4) calculation(5)  th apply blast
           using assms finite_pi' x'_def(1) apply blast
           apply auto
           done
         moreover have "\<pi> x' = \<pi> j" using assms x'_def(1) asm_j(1) jth(1) unfolding core_def valid_partition_def
           by blast
         then show ?thesis using calculation(6) by auto
         next
           case False
           then show ?thesis
              proof(cases "\<pi> j - {j} \<subseteq> neighbors j")
                  case True
                    let ?S = "X \<union> \<pi> j"
                      have pref_S_pi:"\<forall>i\<in>\<pi> j. strict_pref_rel ?S i (\<pi> j)"
                       proof
                          fix i
                          assume asm_i:"i \<in> \<pi> j"
                          obtain j' where j'_def: "j' \<in> X "  using X_def(2) by blast
                          hence "j' \<in> \<pi> x'" using X_def(1) by blast
                          moreover have "j \<notin> \<pi> x'"  using X_def(1) False asm_j(1) by fastforce
                          ultimately have "j \<notin> \<pi> j'" using assms unfolding core_def valid_partition_def
                            using X_def(1) j'_def x'_def(1) by blast
                          hence j'_def':"j' \<notin> \<pi> j" using assms unfolding core_def valid_partition_def 
                            using asm_j by blast
                          show "strict_pref_rel ?S i (\<pi> j)"
                            apply (rule mono_in_neighbor_general[of \<pi> j "Cluster A l" X i ])
                                 apply (rule assms)
                            using asm_j apply blast
                            using X_def(1) apply blast
                            using asm_i apply blast
                            using j'_def j'_def' apply blast
                            using True apply simp
                            done
            qed
            have "blocking_coalition \<pi> ?S" 
              apply(rule blocking_coalition_cluster_general[of j "Cluster A l" "X" \<pi>  ])
              using asm_j(1) apply simp
              using X_def(1) apply simp
              using assms apply simp
              using asm_j(2) X_def(1) apply blast
              using pref_S_pi apply fast
              done
            hence False using assms unfolding core_def in_core_def by fast
            thus ?thesis by blast
          next
            have j_not_in_x:"j \<notin> X" using False .
            case False
            then obtain a where a_def: "a \<in> \<pi> j - {j}" "a \<notin> neighbors j"  by auto
            obtain b where b_def: "b \<in> X" using X_def(2) by blast
            have "val j (\<pi> j) \<le> real 5 / (real 5 + real 2)"
            proof (rule card_val_upper_bound''[of "clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l)) \<union> (clusterNodes(Cluster A l) - {b,j})" 5 "{a,j}" 2 "\<pi> j" j], goal_cases)
              case 1
              have "b \<in> clusterNodes (Cluster A l) " "j \<in> clusterNodes (Cluster A l)" "b \<noteq> j"
              proof (goal_cases)
                case 1
                then show ?case  using X_def(1) b_def by blast
              next
                case 2
                then show ?case  using asm_j(1) by blast
              next
                case 3
                then show ?case  using b_def j_not_in_x by auto
              qed
              hence "card(clusterNodes (Cluster A l) - {b,j}) = 1" using finite_clusterNodes clusterCard_correct[of "Cluster A l"]
                by auto
              moreover have "card (clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l))) = 4"
                using  clusterNodes_inter_empty clusterCard_correct card_Un_disjoint 
                by (simp add: pred_diff)  
              moreover have "(clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l))) \<inter> (clusterNodes (Cluster A l) - {b,j}) = {}"
                      using clusterNodes_inter_empty by auto  
              ultimately show ?case using finite_clusterNodes  card_Un_disjoint[of "clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l))"
"clusterNodes (Cluster A l) - {b,j}"]  
                by (metis finite_Diff finite_Un numeral_Bit0 numeral_Bit1)
            next
              case 2
              have "a \<noteq> j" using a_def(1) by fastforce
              then show ?case by auto
            next 
              case 3
              thus ?case by auto
            next
              case 4
              thus ?case 
              proof
                fix e
                assume asm_e:"e \<in> \<pi> j \<inter> neighbors j"
                hence "e \<in> \<Union> (clusterNodes ` (neighboring_clusters (Cluster A l)))" 
                  by (smt (verit) DiffE Int_iff asm_j(1) neighbors_correct_set)
                moreover have "e \<notin> \<pi> x'" 
                  by (smt (verit, del_insts) Int_iff UNIV_I UN_I X_def(1) asm_e asm_j(1) assms core_def j_not_in_x mem_Collect_eq subsetD valid_partition_def x'_def(1))
                hence "e \<notin> clusterNodes (Cluster C l)" "e \<noteq> b" 
                  using  x'_def(2)
                   X_def(1) b_def by blast+
                moreover have "e \<noteq> j" using asm_e  no_self_neighbor  by blast
                ultimately have "e \<in> (clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l)) \<union>
     clusterNodes (Cluster A l)) - {b, j}" by auto 
                moreover have "b \<in> clusterNodes (Cluster A l)" "b \<notin> clusterNodes (Cluster B l)" "b \<notin> clusterNodes (Cluster B (pred l))"
                  using X_def(1) b_def   clusterNodes_inter_empty by blast+
                moreover have "j \<in> clusterNodes (Cluster A l)" "j \<notin> clusterNodes (Cluster B l)" "j \<notin> clusterNodes (Cluster B (pred l))" 
                  using asm_j(1) clusterNodes_inter_empty by blast+
                ultimately show "e \<in> clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l)) \<union>
     (clusterNodes (Cluster A l) - {b, j})"  by auto
              qed
            next
              case 5
              show ?case using a_def no_self_neighbor[of j] in_its_partition[of \<pi> j "Cluster A l" ]
                 asm_j(1) assms by fast
            next
              case 6
              show ?case using finite_pi'  asm_j(1) assms by blast
            next 
              case 7
              show ?case using finite_clusterNodes finite_subset by blast
            qed
            thus "val j (\<pi> j) < real 4 / real 5" by auto
          qed
        qed
        thus "val j0 (\<pi> j0) < real 4 / real 5" using asm_j' asm_j(2) by fastforce
      qed
      hence "k1 \<notin> clusterNodes(Cluster A l)" "k5 \<notin> clusterNodes (Cluster A l)" 
        using k1_def(2)  k5_def(2) by fastforce+
      hence k_def':"k1 \<in> clusterNodes(Cluster B l)" "k5 \<in> clusterNodes(Cluster B (pred l))" 
        using k1_def(1) k5_def(1) by blast+
      hence   "k1 \<noteq> x'" "k1 \<notin> neighbors x'"  "k5 \<noteq> x'" "k5 \<notin> neighbors x'"
        using n_def  x'_def(1) neighbor_check[of k1 "Cluster B l"  x' "Cluster C l"]
          neighbor_check[of k5 "Cluster B (pred l)"  x' "Cluster C l"] 
          suc2_diff suc_pred suc_diff by auto
      hence "k1 \<notin> \<pi> x'" "k5 \<notin> \<pi> x'" 
        by (metis (no_types, lifting) insertE insert_Diff subset_eq x'_def(1) x'_def(2) x'_def(4))+
      obtain e where "e \<in> X" using X_def(2) by blast
      hence "e \<in> \<pi> x'" "e \<in> clusterNodes (Cluster A l)" using X_def(1) by auto
      then moreover have "k1 \<notin> \<pi> e "  "k5 \<notin> \<pi> e " 
        by (smt (verit, ccfv_threshold) UNIV_I UN_I \<open>k1 \<notin> \<pi> x'\<close> \<open>k5 \<notin> \<pi> x'\<close> assms core_def mem_Collect_eq valid_partition_def x'_def(1))+
      ultimately have k_neighbors:"\<pi> k1 - {k1} \<subseteq> neighbors k1"  "\<pi> k5 - {k5} \<subseteq> neighbors k5" 
        using k1_k5_partition assms k_def'  k1_def(2) k5_def(2) by blast+
      have "clusterNodes (Cluster B (pred (pred l) )) \<subseteq> \<pi> x' \<or> card ( clusterNodes (Cluster B (pred (pred l))) \<inter> \<pi> x') = 1"
      proof (rule ccontr)
        assume asm_cb:"\<not> (clusterNodes (Cluster B (pred (pred l))) \<subseteq> \<pi> x' \<or>
        card (clusterNodes (Cluster B (pred (pred l))) \<inter> \<pi> x') = 1)"
        then obtain b1 where b1_def:"b1 \<in> clusterNodes (Cluster B (pred (pred l) ))" "b1 \<notin> \<pi> x'" by blast
        moreover obtain b2 where b2_def: "b2 \<in>clusterNodes (Cluster B (pred (pred l) ))" "b2 \<in> \<pi> x'"
          using pi_B_pred_pred by blast
        ultimately have "b1 \<noteq> b2" "card({b1,b2}) = 2" "{b1,b2} \<subseteq> clusterNodes (Cluster B (pred (pred l) ))"
          by auto
        moreover have "card (clusterNodes (Cluster B (pred (pred l) ))) = 2" using clusterCard_correct by auto
        ultimately have "clusterNodes (Cluster B (pred (pred l) )) = {b1,b2}" using card_seteq finite_clusterNodes
          by auto
        hence "clusterNodes (Cluster B (pred (pred l))) \<inter> \<pi> x' = {b2}" using b1_def(2) b2_def(2)
          by auto
        hence "card (clusterNodes (Cluster B (pred (pred l))) \<inter> \<pi> x') = 1" by auto
        thus False using asm_cb by auto
      qed
      then show ?thesis
      proof(standard,goal_cases included one_element)
        case included
        obtain j where j_def: "j \<in> clusterNodes (Cluster A l)" 
            "\<forall>x\<in> clusterNodes (Cluster A l). val j (\<pi> j) \<ge> val x (\<pi> x)"
          using finite_clusterNodes[of "Cluster A l"] finite_sup[of "clusterNodes (Cluster A l)" "\<lambda>x. val x (\<pi> x)"] 
          by auto
        show ?thesis
        proof(cases "j \<in> X")
          case True
          have "val j (\<pi> j) \<le>4/7"
          proof -
          obtain nx where  nx_def:"nx \<in> clusterNodes (Cluster A l)" "nx \<notin> X" 
            using X_def(3) by blast
          have "val j (\<pi> x') \<le> real 4 / (real 4 + real 3)"
            proof(rule  card_val_upper_bound''
[of "clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l) - {nx, j}"
              4 "clusterNodes (Cluster B (pred (pred l))) \<union> {j}" 3 "\<pi> x'" j
],goal_cases)
              case 1
              have "card (clusterNodes (Cluster A l)) = 3" "card (clusterNodes (Cluster C l)) = 3"
                using clusterCard_correct by auto
              hence "card (clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l)) = 6"
                using clusterNodes_inter_empty card_Un_disjoint by auto
              moreover have "j \<noteq> nx" using  True nx_def(2) by blast
              ultimately show ?case using nx_def(1) j_def(1) by auto
            next
              case 2
              have "card (clusterNodes (Cluster B (pred (pred l)))) = 2" by auto
              moreover have "j \<notin> clusterNodes (Cluster B (pred (pred l)))"
                using  j_def(1) X_def(1) clusterNodes_inter_empty by auto
              ultimately show ?case by auto
            next
              case 3
              then show ?case by auto
            next
              case 4
              have "\<pi> x' \<subseteq> neighbors x' \<union> {x'}" using x'_def(4) by fastforce
              hence "\<pi> x' \<inter> neighbors j \<subseteq> neighbors x' \<inter> neighbors j \<union> {x'}"
                using IntE  by auto
              moreover have  "neighbors x' \<inter> neighbors j =clusterNodes (Cluster C l) \<union> clusterNodes (Cluster A l) - {x',j}"
                using neighbors_correct_set[of x' "Cluster C l"] neighbors_correct_set[of j "Cluster A l"]  x'_def(1)
                neighbors_intersection[of x' "Cluster C l" j "Cluster A l"] j_def(1) by auto
              ultimately show ?case 
                using X_def(1) nx_def(1) nx_def(2) x'_def(1) by blast    
            next
              case 5
              have "Cluster B (pred (pred l)) \<notin> neighboring_clusters (Cluster A l)" by auto
              hence "clusterNodes (Cluster B (pred (pred l))) \<inter> neighbors j = {} "
                using neighbors_correct_set[of j "Cluster A l"] j_def(1) X_def(1) by auto
              hence "clusterNodes (Cluster B (pred (pred l)))  \<subseteq> \<pi> x' - neighbors j" 
                using included by auto
              then show ?case 
                using X_def(1) True no_self_neighbor by auto
            next
              case 6
              then show ?case using  finite_pi' assms x'_def(1) by blast
            next
              case 7
              then show ?case using finite_clusterNodes by auto
            qed
            moreover have "\<pi> x' = \<pi> j" using x'_def(1) True X_def(1) assms unfolding core_def
            valid_partition_def by blast
            ultimately show ?thesis by auto
          qed
          hence "\<forall>j' \<in> clusterNodes (Cluster A l). val j' (\<pi> j')\<le> 4/7"
            using j_def(2) by auto
          moreover have "\<forall>j'\<in> clusterNodes (Cluster A l). val j' (clusterNodes (Cluster A l)) = 2/3"
            using val_cluster by fastforce
          ultimately have "blocking_coalition \<pi> (clusterNodes (Cluster A l))"
            unfolding blocking_coalition_def strict_pref_rel_def 
            by fastforce
          hence False using assms unfolding core_def in_core_def by auto
          thus ?thesis by auto
        next
          case False
          hence notX : "j \<notin> X" .
          show ?thesis
        proof(cases "\<pi> j - {j} \<subseteq> neighbors j")
          case True
          have "blocking_coalition \<pi> (X \<union> \<pi> j)" 
          proof (rule  blocking_coalition_if_connected[of _ "Cluster A l"], goal_cases)
            case 1
            then show ?case using j_def(1).
          next
            case 2
            then show ?case using j_def(2) .
          next
            case 3
            then show ?case using X_def(1) by blast
          next
            case 4
            then show ?case using X_def(2) .
          next
            case 5
            from notX have "j \<notin> \<pi> x'" using X_def(1) j_def(1) by auto
            moreover obtain e where e_X: "e \<in> X" using X_def(2) by auto
            hence "\<pi> x' = \<pi> e" using assms unfolding core_def valid_partition_def 
              using X_def(1) x'_def(1) by blast
            ultimately have "e \<notin> \<pi> j " 
              by (smt (verit, del_insts) IntE UnionI X_def(1) assms core_def e_X j_def(1) mem_Collect_eq rangeI valid_partition_def)
            then show ?case  using e_X by blast
          next
            case 6
            then show ?case using True .
          next
            case 7
            then show ?case using assms(1) .
          qed
          hence False using assms unfolding core_def in_core_def by auto
          thus ?thesis by auto
        next
          case False
          let ?inter = "\<pi> j \<inter> (clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B ( pred l)))"
          have card_4:"card(?inter) \<le>4" 
            by (metis (no_types, lifting) card_Un_disjoint card_mono clusterCard_correct clusterNodes_inter_empty example_2.Cluster.inject example_2.clusterCard.simps(2) finite_UnI finite_clusterNodes inf_le2 numeral_code(2) pred_diff)
          have  card_2:"card (?inter)\<le>2"
          proof (rule ccontr, goal_cases moreThanTwo)
            case moreThanTwo
            hence "card(?inter) = 3 \<or> card(?inter) = 4" using card_4 by auto
            thus False
            proof(standard,goal_cases card3 card4)
              case card3
              then obtain b where b_def: "clusterNodes (Cluster B l ) \<union> clusterNodes (Cluster B (pred l)) - ?inter = {b}"
                using card_one_diff[of ?inter "clusterNodes (Cluster B l ) \<union> clusterNodes (Cluster B (pred l))"]
                by auto
              then obtain lb lbnot  where lb_def: "b \<in> clusterNodes (Cluster B lb)" "{lb,lbnot}  = {l ,pred l}"
                "lb \<noteq> lbnot"
                using pred_diff by (metis Diff_iff UnE insert_commute singletonI)
              hence "b \<notin> clusterNodes (Cluster B lbnot)" using clusterNodes_inter_empty 
                by auto  
              hence lbnot_subset_inter:"clusterNodes (Cluster B lbnot) \<subseteq> ?inter" using b_def lb_def by fast
              moreover have "k1 \<in> clusterNodes (Cluster B lbnot) \<or> k5 \<in> clusterNodes (Cluster B lbnot) "
                using k_def' lb_def by fast
              then obtain kx where  kx_def:"kx \<in> {k1,k5}" "kx \<in> clusterNodes (Cluster B lbnot)" by auto
              ultimately have "kx \<in> ?inter" by blast
              hence "kx \<in> \<pi> j" by blast
              moreover obtain bnot where bnot_def: "bnot \<in> clusterNodes (Cluster B lb) " "bnot \<noteq> b"
                using numeral_2_eq_2 by auto
              hence "bnot \<in> ?inter" using b_def lb_def 
                by (metis Diff_iff Un_iff not_in_many_clusters' singleton_iff)
              hence "bnot \<in> \<pi> j" by blast
              ultimately have "\<pi> bnot = \<pi> kx" using assms unfolding core_def valid_partition_def 
                by (smt (verit, ccfv_threshold) UnionI j_def(1) mem_Collect_eq rangeI subsetD)
              hence "bnot \<in> \<pi> kx" using assms in_its_partition k_def' kx_def(1)
                bnot_def(1) by blast
              hence "bnot \<in> neighbors kx \<union> {kx}" using kx_def(1) Diff_subset_conv insertE k_neighbors(1) k_neighbors(2) by auto 
              hence "Cluster B lbnot \<in> neighboring_clusters (Cluster B lb)"
                by (smt (verit, best) Un_insert_right bnot_def(1) example_2.Cluster.inject example_2.Node.exhaust example_2.edge_means_neighboring(1) insert_iff kx_def(2) lb_def(3) neighbor_check node_in_cluster sup_bot.right_neutral)
              then show ?case using lb_def(3) by auto
            next
              case card4
              hence "?inter = clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l)) "
                using card_subset_eq[of "clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l))"  ?inter]
                using finite_pi' assms j_def(1) finite_clusterNodes by auto
              hence "k1 \<in> ?inter" "k5 \<in> ?inter" using k_def' by auto
              hence "k1 \<in> \<pi> k5" using assms j_def(1) unfolding core_def valid_partition_def j_def(1)  by blast
              hence "k1 \<in> neighbors k5 \<union> {k5}" using k_neighbors(2) by blast
              hence "Cluster B l \<in> neighboring_clusters (Cluster B (pred l))" using k_def' 
                by (metis (no_types, lifting) Un_iff empty_iff example_2.Cluster.inject insert_iff mem_Collect_eq neighbor_check neighboring_clusters_correct not_in_many_clusters' pred_diff)
              then show ?case using pred_diff 
                by (simp add: neighboring_clusters_correct)
            qed
          qed
          obtain d where d_def: "d \<in> \<pi> j" "d \<noteq> j" "d \<notin> neighbors j" using False by blast 
          obtain a1 where a_def: "a1 \<in> X" using X_def(2) by blast
          have "val j (\<pi> j) \<le> real 3 / (real 3 + real 2)"
          proof (rule  card_val_upper_bound_ineq[of
                "?inter  \<union> (clusterNodes (Cluster A  l) - {a1,j})" 3 "{j,d}" 2 "\<pi> j" j], goal_cases)
            case 1
            have "j \<noteq> a1" 
              using a_def notX by auto 
            hence "card (clusterNodes (Cluster A l) - {a1,j}) = 1"
              using j_def(1) a_def X_def(1) by auto
            then show ?case  using card_2
                card_Un_disjoint[of ?inter "clusterNodes (Cluster A l) - {a1,j}"]
                  finite_pi' j_def(1) assms finite_clusterNodes 
              by force
          next
            case 2
            then show ?case using d_def(2) by auto
          next
            case 3
            then show ?case by auto
          next
            case 4
            from notX have "j \<notin> \<pi> x'" using notX j_def(1) X_def(1) by auto
            hence int_empty:"\<pi> j \<inter> \<pi> x' ={}" using  assms partition_relation
              by (meson j_def(1) x'_def(1)) 
            moreover have "clusterNodes (Cluster C l ) \<subseteq> \<pi> x'" 
              using x'_def(2) by blast
            ultimately have "clusterNodes (Cluster C l ) \<inter> \<pi> j = {}" 
              by auto
            moreover have "a1 \<notin> \<pi> j" 
              using X_def(1) a_def int_empty by auto
            ultimately show ?case using neighbors_correct_set[of j "Cluster A l"]
              j_def(1) by auto
          next
            case 5
            then show ?case using no_self_neighbor in_its_partition d_def assms j_def(1)
              by blast
          next
            case 6
            then show ?case using finite_pi' assms j_def(1) by blast
          next
            case 7
            then show ?case using finite_clusterNodes by blast
          qed
          hence "\<forall>j \<in> clusterNodes (Cluster A l). val j (\<pi> j) \<le> 3/5" 
            using j_def(2) by auto
          moreover have "\<forall>j\<in> clusterNodes (Cluster A l). val j (clusterNodes (Cluster A l)) = 2/3"
            using val_cluster  by fastforce
          ultimately have "blocking_coalition \<pi> (clusterNodes (Cluster A l))"
            unfolding blocking_coalition_def strict_pref_rel_def 
            by fastforce
          hence False using assms unfolding core_def in_core_def by auto
          thus ?thesis by auto
        qed
      qed
    next
      case one_element
      then obtain b4 where b4_def: "clusterNodes (Cluster B (pred (pred l))) \<inter> \<pi> x' = {b4}"
          "b4 \<in> clusterNodes (Cluster B (pred (pred l))) "
        using card_1_singletonE by blast
      have X3:"card X < 3" using psubset_card_mono[of "clusterNodes(Cluster A l)" X]
         finite_clusterNodes X_def(3) by auto
      have X0:"card X > 0" using X_def(2) 
        by (metis X_def(1) card_0_eq finite_Int finite_clusterNodes gr0I)
       have "\<pi> x' = (\<pi> x' \<inter> (neighbors x' \<union> {x'}))" using x'_def(4) by auto
        moreover have "neighbors x' \<union> {x'} = \<Union>(clusterNodes ` (neighboring_clusters (Cluster C l)))"
          using neighbors_correct_set[of x' "Cluster C l"]  x'_def(1) by auto
        ultimately have pi_def:"\<pi> x' = clusterNodes (Cluster C l) \<union> X \<union> {b4}" using  X_def(1) b4_def
            x'_def(2)  by (auto simp del:clusterNodes.simps)
      moreover have X2:"card X = 2"
      proof(rule ccontr,goal_cases X1)
        case X1
        hence "card X = 1" using X3 X0 
          by linarith
        then obtain x0 where x0_def:"X = {x0}" using card_1_singletonE by blast
        hence "\<pi> x' = clusterNodes (Cluster C l) \<union> {x0,b4}" using pi_def by auto
        moreover have "\<pi> x' \<inter> neighbors x' = \<pi> x' - {x'}" using x'_def(4) in_neighboring 
           no_self_neighbor by auto
        moreover have "b4 \<in> clusterNodes (Cluster B (pred (pred l))) " using b4_def by blast
        hence "x0 \<notin> clusterNodes (Cluster C l)" "b4 \<notin> clusterNodes (Cluster C l)"
            "x0 \<noteq> b4"
          using x0_def X_def(3) clusterNodes_inter_empty   by fastforce+
        hence "card (clusterNodes (Cluster C l) \<union> {x0,b4}) = 5" by auto
        then moreover have "card (clusterNodes (Cluster C l) \<union> {x0,b4} - {x'}) = 4"
          using x'_def(1) by auto
        ultimately have "val_graph x' (\<pi> x') = 4/5"  unfolding val_graph_def by auto
        hence "val x' (\<pi> x') = 4/5 " using val_graph_correct 
          by (metis (no_types, lifting) assms(1) finite_pi' x'_def(1))
        hence "val x' (\<pi> x') < val x (\<pi> x)" using x_def(2) by auto
        then show ?case using x'_def(3) asm_x by auto
      qed
      show ?thesis
      proof(standard, goal_cases)
        case 1
        then show ?case using pi_def X2 X_def(3) x'_def(1) b4_def(2) by blast
      next
        case 2
        then show ?case using k_def' k_neighbors k1_def(2) k5_def(2) by blast
      qed
    qed
  qed
qed



lemma A4_A5_not_in_pi:
  fixes \<pi> k l l'
  assumes "\<pi> \<in> core"
  and "\<pi> k \<inter> clusterNodes (Cluster B l) = {k}"
  and "l' = l \<or> l' = Suc l"
  and "\<pi> k - {k} \<subseteq> neighbors k"
shows " \<not> clusterNodes (Cluster A l') \<subseteq> \<pi> k"
proof (rule ccontr,goal_cases subset_pi )
  case subset_pi
  have k_B4:"k \<in> clusterNodes (Cluster B l)" using assms(2) by blast
  have "\<forall>j\<in> clusterNodes (Cluster A l') \<union> clusterNodes ( Cluster C l'). val j (\<pi> j) \<le> 4/5"
  proof
    fix j
    assume "j \<in> clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l') "
    then show "val j (\<pi> j) \<le> 4/5"
    proof(standard,goal_cases A C)
      case A
      hence pi_eq:"\<pi> j = \<pi> k" using assms(1) assms(2) 
        unfolding core_def valid_partition_def 
        by (smt (verit, ccfv_threshold) assms(1) inf_le2 insertCI partition_relation subsetD subset_pi)
      moreover have "val j (\<pi> k) \<le> real 4 / (real 4 + real 1)"
      proof (rule card_val_upper_bound''[of "clusterNodes (Cluster A l') \<union> clusterNodes (Cluster B l) - {j}" _ "{j}"], goal_cases )
        case 1
        then show ?case using A by auto
      next
        case 2
        then show ?case by auto
      next
        case 3
        then show ?case by auto
      next
        case 4
        have "neighboring_clusters (Cluster A l') \<inter> neighboring_clusters (Cluster B l) = {Cluster A l', Cluster B l}"
          using assms(3)  by auto
        hence "neighbors k \<inter> neighbors j = (clusterNodes (Cluster A l') \<union> clusterNodes (Cluster B l)) - {j,k} " 
          using assms(3) neighbors_intersection[of k "Cluster B l" j "Cluster A l'"] clusterNodes_inter_empty assms(2) k_B4 A 
          by (simp add: inf_commute insert_commute)
        hence "(neighbors k \<inter> neighbors j) \<union> {k} = (clusterNodes (Cluster A l') \<union> clusterNodes (Cluster B l)) - {j}"
          using k_B4 A by force
        moreover have "\<pi> k \<inter> neighbors j \<subseteq> (neighbors k \<inter> neighbors j) \<union> {k}" 
          using assms(4) by force
        ultimately show ?case  by auto
      next 
        case 5
        then show ?case using pi_eq in_its_partition assms(1) A no_self_neighbor by blast
      next
        case 6
        then show ?case using finite_pi' assms(1) k_B4 by blast
      next
        case 7
        then show ?case using finite_clusterNodes by auto
      qed
      ultimately show ?thesis by auto
    next
      case C
      hence "j \<notin> neighbors k" 
        by (metis (no_types, lifting) assms(3) example_2.clusterEdge.simps(6) k_B4 neighbor_check suc2_diff)
      moreover have "j \<noteq> k" 
        using C k_B4 by auto
      ultimately have "j \<notin> \<pi> k"  using assms(4) by auto
      hence "\<pi> j \<inter> \<pi> k = {}" 
        by (meson C assms(1) k_B4 partition_relation)
      hence pi_A_empty:"\<pi> j \<inter> clusterNodes (Cluster A l') = {}" using subset_pi by blast
      have "val j (\<pi> j) \<le> real 4 / (real 4 + real 1)"
      proof (rule card_val_upper_bound''[of "clusterNodes (Cluster C l') \<union> clusterNodes (Cluster B (pred (pred l'))) - {j}" _ "{j}"], goal_cases )
        case 1
        then show ?case using C by auto
      next
        case 2
        then show ?case by auto
      next
        case 3
        then show ?case by auto
      next
        case 4
        then show ?case using pi_A_empty C neighbors_correct_set[of j "Cluster C l'"]
          by (auto simp del:clusterNodes.simps)
      next
        case 5
        then show ?case using in_its_partition assms(1) C no_self_neighbor by blast
      next
        case 6
        then show ?case using finite_pi' assms(1) C by blast
      next
        case 7
        then show ?case using no_self_neighbor by auto
      qed
      then show ?case by auto
    qed
   qed
    moreover have "\<forall>j\<in>clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l'). val j (clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l')) = 5/6"
    proof 
      fix j
      assume j_def:"j\<in>clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l')"
      have "val j (clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l')) = f' (card (clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l') - {j}))"
      proof(rule val_in_neighbors[of "clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l')" j],goal_cases)
        case 1
        then show ?case using finite_clusterNodes by auto
      next
        case 2
        then show ?case using j_def .
      next
        case 3
        from j_def show ?case using neighbors_correct_set[of j] by (auto simp del:clusterNodes.simps)
      qed
      moreover have "card (clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l') - {j}) =  5" using j_def by auto
      ultimately show "val j (clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l')) = 5 / 6" unfolding f'_def by auto 
    qed
    ultimately have "\<forall>j \<in>clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l').
           strict_pref_rel (clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l')) j (\<pi> j)"
      unfolding strict_pref_rel_def by auto
    hence "blocking_coalition \<pi> (clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l'))"
      unfolding blocking_coalition_def 
      by (smt (verit, best) Sup_upper Un_least assms(1) cluster_core_min_val emptyE example_2.Cluster.inject example_2.ClusterType.distinct(3) example_2.clusterEdge.simps(3) rangeI)
    then show ?case using assms(1) unfolding core_def in_core_def by auto
  qed

lemma equal_or_disjoint:
  fixes \<pi> x y cx cy
  assumes "\<pi> \<in> core"
  and "x \<in> clusterNodes cx"
  and "y \<in> clusterNodes cy"
and "\<pi> x \<noteq> \<pi> y"
shows "\<pi> x \<inter> \<pi> y = {}"
  using assms by (metis (no_types, lifting) partition_relation)

lemma card_not_2:
  fixes \<pi> k l l'        
  assumes "\<pi> \<in> core"
    and " k \<in> clusterNodes (Cluster B (pred (pred l)))"
    and "\<pi> k - {k} \<subseteq> neighbors k"         
    and "l' = pred l \<or> l' = pred (pred l)"
  shows "card (\<pi> k \<inter> clusterNodes (Cluster A l')) \<noteq> 2"
 proof(cases "\<exists>x5\<in>vertices. clusterNodes (Cluster A l') \<subseteq> \<pi> x5") 
   case True
   then obtain x5  where x5_def: "x5 \<in> vertices" " clusterNodes (Cluster A l' ) \<subseteq>  \<pi> x5" 
     by blast
   then show ?thesis
          proof (cases "k \<in> \<pi> x5")
            case True
            hence "\<pi> k = \<pi> x5" using assms(1) unfolding core_def valid_partition_def 
              using x5_def  by blast
            hence "\<pi> k \<inter> clusterNodes (Cluster A l') = clusterNodes (Cluster A l')" 
              using x5_def(2) by blast
            then show ?thesis by auto
          next
            case False
            hence "\<pi> k \<inter> \<pi> x5 = {}" using assms(1) 
              by (smt (verit, best) UN_iff assms(2) partition_relation x5_def(1))
            hence "\<pi> k \<inter> clusterNodes (Cluster A l') = {}" using x5_def(2) by auto
            then show ?thesis by auto 
          qed
        next        
          case False
          then  obtain  x5 X5 b3   
          where pi_5_def:"\<pi> x5 = clusterNodes(Cluster C l') \<union> X5 \<union> {b3}"
          "X5 \<subseteq> clusterNodes (Cluster A l')" "card X5 = 2"
          "b3 \<in> clusterNodes (Cluster B (pred (pred l')))"
          "x5 \<in> clusterNodes (Cluster C l' )"
            using A_superplayer_aux assms   by meson
          hence "b3 \<notin> neighbors k"
            by (smt (verit, best) assms(2) assms(4) example_2.clusterEdge.simps(5) neighbor_check pred2_diff)
          hence "b3 \<notin> \<pi> k" using k1_k5_partition pi_5_def(4) assms  by auto
          hence "\<pi> x5 \<noteq> \<pi> k" using pi_5_def(1) by blast
          hence "\<pi> x5 \<inter> \<pi> k = {}" using equal_or_disjoint assms(1) 
             assms(2) pi_5_def(5) by blast
          hence "\<pi> k \<inter> clusterNodes (Cluster A l') \<subseteq> clusterNodes (Cluster A l') - X5"
            using disjoint_iff pi_5_def(1) by auto
          moreover have "card (clusterNodes (Cluster A l') - X5) = 1 " using pi_5_def(2,3) clusterCard_correct[of "Cluster A l'"]
            by (simp add: card_Diff_subset finite_subset)       
          ultimately show ?thesis 
            by (metis card_mono finite_Diff finite_clusterNodes numeral_le_one_iff semiring_norm(69)) 
        qed
lemma pred_suc_diff:
"pred l \<noteq> Suc l" apply (induct l) apply auto done  
                                                         
lemma 
"finite S \<Longrightarrow> x \<in> S \<Longrightarrow> card S \<ge> 1" 
  using card_gt_0_iff less_eq_Suc_le by auto 
lemma inter_empty:"Y \<inter> Z = {} \<Longrightarrow> (Y\<inter> S) \<inter> (Z \<inter> S) = {}"
  by auto

lemma A_superplayer:                                                         
  fixes \<pi>
  assumes "\<pi> \<in> core"                      
  shows "\<exists>x\<in> vertices. clusterNodes (Cluster A l) \<subseteq> \<pi> x"
proof (rule ccontr, goal_cases asm_s)
  case asm_s                                              
  then obtain x' X b4 k5 k1 where thms: 
      "x'\<in> clusterNodes (Cluster C l)" "X \<subseteq> clusterNodes(Cluster A l)" 
        "b4 \<in> clusterNodes (Cluster  B (pred (pred l)))"
         "\<pi> x' = clusterNodes (Cluster C l) \<union> X \<union> {b4}" 
        "card X = 2"
      "k5\<in>clusterNodes (Cluster B (pred l))"
        "real 4 / real 5 \<le> val k5 (\<pi> k5)"  "\<pi> k5 - {k5} \<subseteq> neighbors k5"
        "k1\<in>clusterNodes (Cluster B  l)"
        "real 4 / real 5 \<le> val k1 (\<pi> k1)"  "\<pi> k1 - {k1} \<subseteq> neighbors k1"
    using A_superplayer_aux assms  by (smt (verit, ccfv_threshold))
  hence inters:"X = \<pi> x' \<inter> clusterNodes (Cluster A l)"
    "{b4} = \<pi> x' \<inter> clusterNodes (Cluster  B (pred (pred l)))"
    using clusterNodes_inter_empty by auto
  have "k1 \<noteq> k5" using thms(6) thms(9) clusterNodes_inter_empty pred_diff by auto
  moreover then have  "k1 \<notin> neighbors k5" using thms(9) thms(6) neighbor_check 
    example_2.clusterEdge.simps(5) pred_diff by presburger
  ultimately have "k1 \<notin> \<pi> k5" using thms(8) by auto
  hence k1_k5_disjoint: "\<pi> k1 \<inter> \<pi> k5 = {}" 
    by (meson assms partition_relation thms(6) thms(9))
  from thms(2) have "X \<inter> clusterNodes (Cluster C l ) = {}" using clusterNodes_inter_empty
            by auto
        hence  Cl_Un_X:"card (clusterNodes (Cluster C l ) \<union> X) = 5" 
          using card_Un_disjoint[of "clusterNodes (Cluster C l )" X] 
              finite_clusterNodes thms(5) finite_subset
        by fastforce
      moreover have "b4 \<notin> clusterNodes (Cluster C l)" "b4 \<notin> X" using not_in_many_clusters' 
        thms(2) thms(3)
        by auto
      ultimately have "card(clusterNodes (Cluster C l) \<union> X \<union> {b4}) = 6" 
        using finite_clusterNodes[of "Cluster C l"] finite_clusterNodes[of "Cluster A l"]
        thms finite_subset[of  X "clusterNodes (Cluster A l)"] by auto
      hence card_pi_x':"card (\<pi> x') = 6" using thms(4) by auto
      have "\<forall>j \<in> X. val j (\<pi> j) = 4/6"
      proof 
        fix j
        assume asm_j :"j \<in> X"
        hence j_def:"j \<in> clusterNodes (Cluster A l)" using thms(2) by auto
        hence "neighbors j = \<Union>(clusterNodes ` neighboring_clusters (Cluster A l)) - {j}"
          using neighbors_correct_set[of j "Cluster A l"] by auto
        have "\<pi> x' \<inter> neighbors j = (clusterNodes (Cluster C l) \<inter> neighbors j)
          \<union>  (X \<inter> neighbors j) \<union> ({b4}\<inter> neighbors j) "
          using thms(4) by auto
        moreover have "clusterNodes (Cluster C l) \<inter> neighbors j = clusterNodes (Cluster C l) - {j}"
          using neighbors_correct_set[of j "Cluster A l"] j_def by auto
        moreover have "X \<inter> neighbors j = X - {j}" 
          using neighbors_correct_set[of j "Cluster A l"] j_def inters(1) by auto
        moreover have "b4 \<notin> neighbors j" using thms(3) not_in_many_clusters'
          using neighbors_correct_set[of j "Cluster A l"] j_def neighbor_check pred2_diff suc_pred
          by (smt (verit, best) example_2.clusterEdge.simps(2))
        ultimately have "\<pi> x' \<inter> neighbors j = clusterNodes (Cluster C l) \<union> X - {j} " by auto
        hence "card(\<pi> x' \<inter> neighbors j) = 4" using Cl_Un_X asm_j by auto
        hence "val_graph j (\<pi> x') = 4/6 " unfolding val_graph_def using card_pi_x' by auto
        hence "val j (\<pi> x') = 4/6" using val_graph_correct finite_pi'[of \<pi> x' "Cluster C l"] assms thms(1)
          by auto
        moreover have " j \<in> \<pi> x'" using asm_j thms(4) by auto
        hence "\<pi> x' = \<pi> j" using assms j_def(1) thms(1) unfolding core_def valid_partition_def by blast
        ultimately show " val j (\<pi> j) = 4 / 6 " by simp
      qed
      obtain k where k_def: "k \<in> clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster B (pred (pred l)))"
        "val k (\<pi> k)\<ge> 4/5"           
        using cluster_core_min_val[of "Cluster A (pred l)" "Cluster B (pred (pred l))"] assms 
        unfolding f'_def by (auto simp del:clusterNodes.simps)
      have k_A5: "k \<in> clusterNodes (Cluster A (pred l) )"  
      proof (rule ccontr)
        assume "k \<notin> clusterNodes (Cluster A (pred l))"
        hence k_B4:"k \<in> clusterNodes (Cluster B (pred (pred l)))" using k_def(1) by auto
        show False
        proof (cases "k \<in> \<pi> x'")
          case True
          hence k_b4_eq:"k = b4" using k_B4 inters(2) by blast
          have "clusterNodes (Cluster C l ) \<subseteq> neighbors b4" using thms(3)
              cluster_neighbor_check[of b4 "Cluster B (pred (pred l))" "Cluster C l"] by auto
          moreover have "clusterNodes (Cluster A l ) \<inter> neighbors b4 = {}" using 
              cluster_not_neighbor_check[of b4 "Cluster B (pred (pred l))" "Cluster A l"]
            thms(3) clusterEdge.simps(4) pred2_diff  by fastforce
          hence "X \<inter> neighbors b4 = {}" using thms(2) by auto
          ultimately have "\<pi> x' \<inter> neighbors b4 = clusterNodes (Cluster C l)"
            using no_self_neighbor[of b4] thms(4) by blast
          hence "card (\<pi> x' \<inter> neighbors b4) = 3" by auto
          hence "val_graph b4 (\<pi> x') = 3/6" unfolding val_graph_def 
            using card_pi_x' by auto
          hence "val b4 (\<pi> x') = 3/6" using val_graph_correct finite_pi' thms(1) assms 
            by (smt (verit, best))
          moreover have "\<pi> x' = \<pi> k" using True assms unfolding core_def valid_partition_def 
            using k_B4 thms(1) by blast
          ultimately have "val k (\<pi> k) = 3/6" using k_b4_eq by force           
          then show ?thesis using k_def(2) by auto
        next
          case False
          hence "k \<noteq> b4"  by (simp add: thms(4))
          hence "card ({k,b4}) = 2" by auto
          moreover have "{k,b4} \<subseteq> clusterNodes (Cluster B (pred (pred l))) " using k_B4 thms(3) by blast
          moreover have "card (clusterNodes (Cluster B (pred (pred l)))) = 2" by auto
          ultimately have b4_def:"clusterNodes (Cluster B (pred (pred l))) = {k,b4}" 
            by (metis card_subset_eq finite_clusterNodes)
          have k_neighbors:"\<pi> k - {k} \<subseteq> neighbors k"
          proof (rule ccontr)
            assume "\<not> \<pi> k - {k} \<subseteq> neighbors k"
            then obtain k0 where k0_def: "k0 \<in> \<pi> k" "k0 \<noteq> k" "k0 \<notin> neighbors k" by blast
            have "val k (\<pi> k) \<le> real 6 / (real 6+ real 2)"
            proof (rule card_val_upper_bound''[of "clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster A (pred (pred l)))" 6 "{k0,k}" 2 "\<pi> k" k], goal_cases)
              case 1
              then show ?case by auto
            next
              case 2
              then show ?case using k0_def(2) by auto
            next
              case 3
              then show ?case by auto
            next
              case 4
              from False have "\<pi> k \<inter> \<pi> x' = {}" 
                by (meson assms k_B4 partition_relation thms(1))
              hence "\<pi> k \<inter> clusterNodes (Cluster C l) = {}" "b4 \<notin> \<pi> k" "k \<notin> neighbors k"
                using no_self_neighbor  by (auto simp add:thms(4))
              hence  "\<pi> k \<inter> neighbors k \<inter> clusterNodes (Cluster C l) = {}" "\<pi> k \<inter> neighbors k \<inter> clusterNodes (Cluster B (pred (pred l))) = {} "
                using b4_def by auto
              then show ?case using neighbors_correct_set k_B4 by (auto simp del:clusterNodes.simps)
            next
              case 5
              then show ?case using k0_def no_self_neighbor in_its_partition assms k_B4 
                by blast
            next
              case 6
              then show ?case using finite_pi' assms k_B4 by blast
            next
              case 7
              then show ?case using finite_clusterNodes by auto
            qed
          then show False using k_def(2) by auto
        qed         
        moreover have "\<pi> k \<inter> clusterNodes (Cluster B (pred (pred l))) = {k}" 
          by (smt (verit, ccfv_SIG) False Int_Un_eq(3) Int_insert_right UnI1 UnI2 thms assms b4_def boolean_algebra.conj_zero_right in_its_partition insertI1 partition_relation thms(1))
        ultimately have A4_A5: "\<not> clusterNodes (Cluster A (pred l)) \<subseteq> \<pi> k" 
          "\<not> clusterNodes (Cluster A (pred (pred l))) \<subseteq> \<pi> k"
          using A4_A5_not_in_pi[of \<pi> k "pred (pred l)"]
          pred_suc suc_pred assms by metis+
        hence "\<pi> k \<inter> clusterNodes (Cluster A (pred l)) \<subset> clusterNodes (Cluster A (pred l)) "
          "\<pi> k \<inter> clusterNodes (Cluster A (pred (pred l))) \<subset> clusterNodes (Cluster A (pred (pred l))) "
          by blast+
        hence "card (\<pi> k \<inter> clusterNodes (Cluster A (pred l))) < 3"
            "card (\<pi> k \<inter> clusterNodes (Cluster A (pred (pred l)))) < 3"
          using psubset_card_mono finite_clusterNodes clusterCard_correct 
          by (metis example_2.clusterCard.simps(1))+
        moreover have "card (\<pi> k \<inter> clusterNodes (Cluster A (pred l))) \<noteq> 2"
          "card (\<pi> k \<inter> clusterNodes (Cluster A (pred (pred l)))) \<noteq> 2"
          using assms card_not_2 k_B4 k_neighbors by blast+
        ultimately have "card (\<pi> k \<inter> clusterNodes (Cluster A (pred l))) \<le> 1"
            "card (\<pi> k \<inter> clusterNodes (Cluster A (pred (pred l)))) \<le> 1"
          by linarith+
        hence *:"card (\<pi> k \<inter> ( clusterNodes (Cluster A (pred (pred l))) \<union>
            clusterNodes (Cluster A (pred l))))\<le> 2"
          using card_Un_le[of "\<pi> k \<inter> clusterNodes (Cluster A (pred (pred l)))"
                    "\<pi> k \<inter> clusterNodes (Cluster A (pred l))"]
          by (smt (verit, ccfv_SIG) add_le_mono boolean_algebra.conj_disj_distrib le_trans nat_1_add_1)
        have "val k (\<pi> k) \<le> real 2 / (real 2 + real 1)"
        proof (rule card_val_upper_bound_ineq[of "\<pi> k \<inter> (clusterNodes (Cluster A (pred (pred l))) \<union>
            clusterNodes (Cluster A (pred l)))" 2 "{k}" 1 "\<pi> k" k], goal_cases)
          case 1
          then show ?case using * .
        next
          case 2                                              
          then show ?case by auto
        next
          case 3
          then show ?case by auto
        next
          case 4
          from False have inter_k_x'_empty: "\<pi> k \<inter> \<pi> x' = {}" 
            by (meson assms k_B4 partition_relation thms(1))
          hence "\<pi> k \<inter> clusterNodes (Cluster C l) = {}" using thms(4) by auto
          moreover have "k \<notin> neighbors k" "b4 \<notin> \<pi> k"
            using no_self_neighbor inter_k_x'_empty thms(4) by auto
          hence "\<pi> k \<inter> neighbors k \<inter> clusterNodes(Cluster B (pred (pred l))) = {}"
            using b4_def by auto
          ultimately show ?case using neighbors_correct_set[of k "Cluster B (pred (pred l))"] k_B4 
            using suc_pred pred_suc by auto
        next
          case 5
          then show ?case using in_its_partition assms k_B4 no_self_neighbor by blast
        next
          case 6
          then show ?case using finite_pi' assms k_B4 by blast
        next
          case 7
          then show ?case using finite_clusterNodes by blast
        qed
        then show False using k_def(2) by auto
      qed
    qed
      obtain k where k_def': "k \<in> clusterNodes (Cluster A (pred l))"                                
                  "\<forall>x \<in> clusterNodes (Cluster A (pred l)). val k (\<pi> k) \<ge> val x (\<pi> x)"
         using finite_clusterNodes[of "Cluster A (pred l)"]  finite_sup[of "clusterNodes(Cluster A (pred l))" "\<lambda>x. val x (\<pi> x)"]
         using k_A5 by blast    
       hence k_val:"val k (\<pi> k) \<ge> 4/5" using k_A5 k_def(2) by auto        
    have k_k5_not_co:"k \<notin> \<pi> k5"
    proof (rule ccontr, goal_cases k_k5)
      case k_k5
      hence eq_k_k5:"\<pi> k = \<pi> k5" using assms thms(6) k_def'(1) unfolding core_def valid_partition_def  
        by blast          
      have val_k_ubound:"val k (\<pi> k) \<ge> f' 4" unfolding f'_def using k_val by auto 
      hence "card (\<pi> k \<inter> neighbors k) \<ge> 4" using card_val_lower_bound 
        by (smt (verit, del_insts) Diff_empty eq_k_k5 finite_Diff_insert finite_neighbors k_k5 rev_finite_subset thms(8))
      moreover have "\<pi> k \<inter> (neighbors k \<union> {k}) = (\<pi> k \<inter> neighbors k) \<union> {k} "
          using  eq_k_k5 k_k5 by auto
      ultimately have "card (\<pi> k \<inter> (neighbors k \<union> {k})) \<ge> 5" using no_self_neighbor 
          by (smt (verit, best) Int_iff Suc_leI UnI2 Un_Int_eq(3) assms card_mono card_subset_eq eval_nat_numeral(3) finite_Int finite_pi' inf_le2 insertI1 k_def'(1) le_eq_less_or_eq le_trans)
        moreover have " \<pi> k \<inter> (neighbors k \<union> {k}) \<subseteq> (neighbors k5 \<union> {k5}) \<inter> (neighbors k \<union> {k}) " using thms(8)  eq_k_k5 by auto
        moreover have "... \<subseteq> (neighbors k \<inter> neighbors k5) \<union> {k,k5} " by force
        moreover have "neighboring_clusters (Cluster A (pred l)) \<inter> neighboring_clusters (Cluster B (pred l)) = 
{Cluster A (pred l), Cluster B (pred l)}" using pred_suc_diff by auto
          hence
"(neighbors k \<inter> neighbors k5) \<union> {k,k5} = clusterNodes (Cluster A (pred l)) \<union>  clusterNodes (Cluster B (pred l))" using neighbors_intersection[of k "Cluster A (pred l)" k5 "Cluster B (pred l)" ] k_def'(1) thms(6)
            by auto
          moreover have "card (clusterNodes (Cluster A (pred l)) \<union>  clusterNodes (Cluster B (pred l))) = 5 " by auto
          ultimately have " \<pi> k \<inter> (neighbors k \<union> {k}) \<subseteq> clusterNodes (Cluster A (pred l)) \<union>  clusterNodes (Cluster B (pred l)) "
              "card (\<pi> k \<inter> (neighbors k \<union> {k})) \<ge> card (clusterNodes (Cluster A (pred l)) \<union>  clusterNodes (Cluster B (pred l))) "
            by auto
          hence "\<pi> k \<inter> (neighbors k \<union> {k}) = clusterNodes (Cluster A (pred l)) \<union>  clusterNodes (Cluster B (pred l))"
            using card_mono finite_clusterNodes  by (simp add: card_seteq)
          hence pi_k_neighbors_elems:"\<pi> k \<inter> neighbors k = clusterNodes (Cluster A (pred l)) \<union>  clusterNodes (Cluster B (pred l)) - {k} "
            using no_self_neighbor by auto
          hence card_pi_neighbors_4:"card (\<pi> k \<inter> neighbors k) = 4" using k_def'(1) by auto
          moreover have "val_graph k (\<pi> k) \<ge> 4/5" using val_k_ubound  val_graph_correct finite_pi' assms k_def'(1)
            unfolding f'_def by (metis (no_types, lifting) k_val)
          ultimately have "card (\<pi> k) \<le>  5" unfolding val_graph_def  
            by (smt (verit, ccfv_SIG) assms card_val_upper_bound divide_cancel_left eq_k_k5 f'_def finite_pi' k_def'(1) k_k5 numeral_Bit1 numeral_One numeral_code(2) of_nat_1 of_nat_le_iff of_nat_numeral val_graph_correct val_graph_def)
          hence "card (\<pi> k - neighbors k) \<le> 1 " using  card_pi_neighbors_4 card_Un_disjoint[of "\<pi> k \<inter> neighbors k" "\<pi> k - neighbors k"] finite_pi' assms k_def'(1)                                                
            by (metis (no_types, lifting) Int_Diff_Un Int_Diff_disjoint finite_Diff finite_Int nat_add_left_cancel_le numeral_Bit1 numeral_code(2))
          moreover have "k \<in> \<pi> k -neighbors k" using eq_k_k5 k_k5 no_self_neighbor by auto  
          then moreover have " card (\<pi> k - neighbors k) \<ge> 1 "   using card_gt_0_iff less_eq_Suc_le finite_pi' assms k_def'(1)
            by (metis (no_types, lifting) One_nat_def empty_iff finite_Diff)                                                      
          ultimately have "\<pi> k -neighbors k = {k}"                                                                        
            by (metis (no_types, lifting) Diff_eq_empty_iff Diff_insert Un_insert_right \<open>\<pi> k \<inter> (neighbors k \<union> {k}) = clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster B (pred l))\<close> \<open>card (\<pi> k) \<le> 5\<close> \<open>card (clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster B (pred l))) = 5\<close> assms card_seteq finite_pi' inf_le1 inf_le2 insert_Diff k_def'(1) sup_bot.right_neutral)         
          hence pi_k_def:"\<pi> k = clusterNodes (Cluster A (pred l)) \<union>  clusterNodes (Cluster B (pred l)) "  using  pi_k_neighbors_elems
            by (metis (no_types, lifting) Int_Diff_Un \<open>\<pi> k \<inter> (neighbors k \<union> {k}) = \<pi> k \<inter> neighbors k \<union> {k}\<close> \<open>\<pi> k \<inter> (neighbors k \<union> {k}) = clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster B (pred l))\<close>)
          have "\<forall>j \<in> clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster C (pred l)). val j (\<pi> j) \<le> 4/5"
          proof (standard, goal_cases A_C)
            case (A_C j)    
            then show ?case
            proof (standard, goal_cases A C)
              case A
              hence "j \<in> \<pi> k" using pi_k_def by auto
              hence "\<pi> j = \<pi> k" using assms k_def'(1) A unfolding core_def valid_partition_def by blast      
              moreover have "\<pi> k \<inter> neighbors j = clusterNodes (Cluster A (pred l)) \<union>  clusterNodes (Cluster B (pred l)) - {j}"
                using A neighbors_correct_set pi_k_def by (auto simp del : clusterNodes.simps)
              hence "card (\<pi> k \<inter> neighbors j) = 4" using A by auto    
              hence "val_graph j (\<pi> k)= 4/5" using pi_k_def unfolding val_graph_def by auto
              hence "val j (\<pi> k) = 4/5" using val_graph_correct finite_pi' assms k_def'(1)  by (smt (verit))
              ultimately show ?case by auto                                           
            next
              case C                                                                                      
              hence "j \<notin> \<pi> k" using pi_k_def clusterNodes_inter_empty by auto
              hence "\<pi> j \<inter> \<pi> k = {}"                               
                by (meson C assms k_def'(1) partition_relation)
              hence not_A:"\<pi> j \<inter> clusterNodes (Cluster A (pred l)) = {}" using pi_k_def by auto
              have "val j (\<pi> j) \<le> real 4 / (real 4 + real 1)"
              proof (rule  card_val_upper_bound''[of "clusterNodes (Cluster C (pred l)) \<union> clusterNodes (Cluster B (pred (pred (pred l)))) - {j}" _ "{j}"], goal_cases)
                case 1                 
                then show ?case using C by auto    
              next
                case 2
                then show ?case by auto
              next
                case 3                                  
                then show ?case by auto                              
              next
                case 4          
                then show ?case using not_A neighbors_correct_set C by (auto simp del:clusterNodes.simps)     
              next
                case 5             
                then show ?case using in_its_partition assms C no_self_neighbor by blast         
              next
                case 6                                   
                then show ?case using finite_pi' assms C  by blast    
              next
                case 7
                then show ?case using finite_clusterNodes by auto
              qed          
              then show ?case by auto
            qed   
          qed
          moreover have "\<forall>j\<in> clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster C (pred l)). val j ( clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster C (pred l))) = 5/6"
          proof(standard,goal_cases A_C)
            case (A_C j)                                                                                
            have "val j (clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster C (pred l))) =
f' (card (clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster C (pred l)) - {j}))"                           
            proof (rule  val_in_neighbors[of "clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster C (pred l))" j], goal_cases)
              case 1
              then show ?case by auto
            next            
              case 2                       
              then show ?case using A_C  by auto  
            next    
              case 3
              then obtain c where " c = Cluster A (pred l) \<or> c = Cluster C (pred l)" "j \<in> clusterNodes c"
                using A_C by blast             
              then show ?case                                                                     
                  using  neighbors_correct_set[of j] by(auto simp del:clusterNodes.simps)        
              qed
            then show ?case unfolding f'_def using A_C by auto
          qed                          
         ultimately have "\<forall>j\<in>clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster C (pred l)).
             val j (\<pi> j) < val j (clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster C (pred l))) " 
           by auto
         hence "blocking_coalition \<pi> (clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster C (pred l))) "
           unfolding blocking_coalition_def 
           by (smt (verit, ccfv_SIG) Un_iff Un_subset_iff Union_upper insert_absorb insert_not_empty k_A5 rangeI strict_pref_rel_def)
         thus False using assms unfolding core_def in_core_def by auto
       qed
       have "\<pi> k - {k} \<subseteq> neighbors k"             
       proof(rule ccontr,goal_cases asm)
         case asm  
         then obtain k0 where k0_def: "k0 \<in> \<pi> k" "k0 \<noteq> k" "k0 \<notin> neighbors k" by blast
         have "val k (\<pi> k) \<le> real 7 / (real 7 + real 2)"
         proof(rule card_val_upper_bound''[of "neighbors k - {k5,b4}" _ "{k,k0}"],goal_cases)
           case 1                                                                   
           have "k5 \<in> neighbors k" 
             using neighbor_check[of  k5 "Cluster B (pred l)" k "Cluster A (pred l)"] k_def'(1) thms(6) clusterNodes_inter_empty
              clusterEdge.simps(2) by blast                                           
             moreover have "b4 \<in> neighbors k" 
               using neighbor_check[of b4 "Cluster B (pred (pred l))" k "Cluster A (pred l)"] thms(3) k_def'(1) clusterNodes_inter_empty  
               by auto       
             moreover have "card (neighbors k) = 9" using card_neighbors_A' k_def'(1) by auto
             ultimately show ?case 
               by (smt (verit, ccfv_SIG) Diff_empty Diff_insert2 card_Diff_insert diff_add_inverse diff_add_inverse2 example_2.Cluster.inject insert_absorb not_in_many_clusters' numeral_Bit1 numeral_code(2) one_plus_numeral pred_diff semiring_norm(2) semiring_norm(4) semiring_norm(8) singleton_iff thms(3) thms(6))
         next                         
           case 2    
           then show ?case using k0_def(2) by auto
         next
           case 3            
           then show ?case by auto
         next
           case 4     
           have "k \<notin> \<pi> x'" using thms(1,2,3,4) clusterNodes_inter_empty 
              by (smt (verit, ccfv_threshold) IntE Un_iff example_2.Cluster.inject inters(2) k_def'(1) not_in_many_clusters' pred_diff subsetD) 
            moreover have "\<pi> x' = \<pi> b4" using thms(1,4) assms unfolding core_def valid_partition_def 
              by (metis (no_types, lifting) IntE assms insertCI inters(2) partition_relation)              
            ultimately have "k \<notin> \<pi> b4" by auto
            hence "b4 \<notin> \<pi> k" using partition_relation assms thms(3) k_def'(1) 
              by (metis (no_types, lifting) in_its_partition)  
            moreover have "k5 \<notin> \<pi> k"  using  k_k5_not_co  partition_relation assms  k_def'(1) thms(6)
              by (metis (no_types, lifting) in_its_partition)  
            ultimately show ?case by auto                          
         next                                                                       
           case 5
           then show ?case using in_its_partition assms  k_def'(1) no_self_neighbor k0_def  by blast                   
         next
           case 6
           then show ?case  using finite_pi' assms k_def'(1) by blast  
         next
           case 7                                                                               
           then show ?case using finite_neighbors by blast
         qed
         then show ?case using k_val by auto
       qed                             
       have A5_pi_k: "clusterNodes (Cluster A (pred l)) \<subseteq> \<pi> k"
       proof (rule ccontr, goal_cases asm)
         case asm                                                                    
         hence "\<forall>i \<in> \<pi> k. strict_pref_rel (clusterNodes (Cluster A (pred l)) \<union>  \<pi> k) i (\<pi> k)"
           using mono_in_neighbor'[of \<pi> k "Cluster A (pred l)" _ ] assms k_def'(1)  
            \<open>\<pi> k - {k} \<subseteq> neighbors k\<close> by blast
         hence "blocking_coalition \<pi> (clusterNodes (Cluster A (pred l)) \<union>  \<pi> k)" using
            blocking_coalition_cluster assms  k_def' by blast
         then show False using assms unfolding core_def in_core_def by auto                       
       qed
       have C_more_2: "card (\<pi> k5 \<inter> clusterNodes (Cluster C (Suc l))) \<ge> 2"
       proof (rule ccontr,goal_cases C2)          
         case C2                
         have "\<pi> k5 \<inter> \<pi> x' = {}" 
             by (smt (verit) assms card_not_2 equal_or_disjoint example_2.ClusterNumber.exhaust example_2.pred.simps(1) example_2.pred.simps(2) example_2.pred.simps(3) example_2.pred.simps(4) example_2.pred.simps(5) inters(1) thms(1) thms(5) thms(6) thms(8))
         hence "\<pi> k5 \<inter> X = {}"     
           using inters(1) by blast  
         hence "\<pi> k5 \<inter> clusterNodes (Cluster A l) \<subseteq> clusterNodes (Cluster A l) - X " by auto
         moreover have "card(clusterNodes (Cluster A l) - X) = 1" 
           by (metis card_Diff_subset clusterCard_correct diff_add_inverse example_2.clusterCard.simps(1) finite_clusterNodes finite_subset nat_1_add_1 numeral_Bit1 numeral_One thms(2) thms(5))
         ultimately have "card (\<pi> k5 \<inter> clusterNodes (Cluster A l)) \<le> 1"
           using card_mono finite_clusterNodes by (metis finite_Diff)
         moreover have "\<pi> k5 \<inter> clusterNodes (Cluster A (pred l)) = {}" 
           using \<open>clusterNodes (Cluster A (pred l)) \<subseteq> \<pi> k\<close> assms equal_or_disjoint k_def'(1) k_k5_not_co thms(6) by blast
         hence "card (\<pi> k5 \<inter> clusterNodes (Cluster A (pred l))) = 0" by auto 
         moreover have  "card (\<pi> k5 \<inter> clusterNodes (Cluster C (Suc l))) \<le> 1" using C2 by auto
         moreover have  "card (\<pi> k5 \<inter> clusterNodes (Cluster B (pred l))) \<le> 2" 
           by (metis card_mono clusterCard_correct example_2.clusterCard.simps(2) finite_clusterNodes inf_le2)                         
         ultimately have "card (\<pi> k5 \<inter> clusterNodes (Cluster A (pred l)) \<union>
      (\<pi> k5 \<inter> clusterNodes (Cluster A l) \<union>
       (\<pi> k5 \<inter> clusterNodes (Cluster B (pred l)) \<union> \<pi> k5 \<inter> clusterNodes (Cluster C (local.Suc l))))) \<le> 4"
           using card_Un_disjoint[OF finite_subset[of _ "\<pi> k5",OF _ finite_pi'[of \<pi> k5 "Cluster B (pred l) ", OF assms thms(6) ]]
 finite_subset[of _ "\<pi> k5",OF _ finite_pi'[of \<pi> k5 "Cluster B (pred l) ", OF assms thms(6) ]]
       inter_empty[of _ _"\<pi> k5"], OF _ _  clusterNodes_inter_empty, OF lattice_class.inf_sup_ord(2) lattice_class.inf_sup_ord(2)                                                              
       ] pred_diff 
           by (smt (z3) One_nat_def Un_commute add_0 card_Un_le le_Suc_eq le_zero_eq numeral_3_eq_3 numeral_plus_numeral numerals(1) plus_1_eq_Suc semiring_norm(2) semiring_norm(4))
         hence "card (\<pi> k5 \<inter>  \<Union>(clusterNodes ` (neighboring_clusters (Cluster B (pred l))))) \<le> 4"
           by (auto simp del:clusterNodes.simps  simp add: Int_Un_distrib)
         moreover have "k5 \<in>  \<Union>(clusterNodes ` (neighboring_clusters (Cluster B (pred l)))) " 
           using thms(6) by auto 
         moreover have "\<pi> k5 \<inter> neighbors k5 = (\<pi> k5 \<inter>  \<Union>(clusterNodes ` (neighboring_clusters (Cluster B (pred l))))) - {k5}"
           by (smt (verit) Int_Diff neighbors_correct_set thms(6))
          ultimately have "card (\<pi> k5 \<inter> neighbors k5) \<le> 3" 
           unfolding  neighbors_correct_set[OF thms(6)]                              
           using in_its_partition[OF assms thms(6)]       
           by (auto simp del:clusterNodes.simps simp add: thms(6) clusterNodes_inter_empty)  
         hence "val k5 (\<pi> k5) \<le> 3/4" using card_val_upper_bound in_its_partition[OF assms thms(6)]
           unfolding f'_def 
           by (smt (verit, ccfv_SIG) assms finite_pi' numeral_Bit1 numeral_One of_nat_1 of_nat_numeral thms(6))                    
         then show ?case using thms(7) by auto                                                                        
       qed
       have "\<exists>a2 \<in> vertices. clusterNodes (Cluster A (Suc l)) \<subseteq> \<pi> a2"
       proof (rule ccontr,goal_cases asm)
         case asm
         then obtain x0  X0 b0 where O_def: "x0 \<in> clusterNodes (Cluster C (Suc l))"
          "X0 \<subseteq> clusterNodes (Cluster A (Suc l))" "b0 \<in> clusterNodes (Cluster B (pred l))"
          "card X0 = 2"  "\<pi> x0 = clusterNodes (Cluster C (Suc l)) \<union> X0 \<union> {b0}"
           using A_superplayer_aux[OF assms]   by (metis (no_types, lifting) pred_suc)
         then obtain a where a_def:"a \<in> X0"  by (meson card_2_iff')
         hence "a \<in> \<pi> b0" using O_def assms unfolding core_def valid_partition_def 
           by (smt (verit, ccfv_threshold) Un_iff UnionI insertI1 mem_Collect_eq rangeI)
         moreover have "a \<notin> neighbors b0" using a_def assms O_def
 neighbor_check[of a "Cluster A (Suc l)" b0 "Cluster B (pred l)"]
           by (metis example_2.clusterEdge.simps(4) in_mono pred_suc_diff suc_diff suc_pred)
         moreover have "a \<noteq> b0" using clusterNodes_inter_empty a_def O_def by auto
         ultimately have "b0 \<noteq> k5" using Diff_insert0 subsetD thms(8) by auto
         obtain c where "c \<in> clusterNodes (Cluster C (Suc l)) \<inter> \<pi> k5" 
           by (metis Int_commute \<open>2 \<le> card (\<pi> k5 \<inter> clusterNodes (Cluster C (local.Suc l)))\<close> add_0 add_leE all_not_in_conv card_Un_disjoint diff_add_inverse2 finite_clusterNodes finite_subset inf_bot_right inf_le1 not_less_eq_eq numeral_eq_Suc sup_bot.right_neutral)
         hence "c \<in> \<pi> k5" "c \<in> \<pi> x0" using O_def by blast+
         hence "\<pi> k5 = \<pi> c "  "\<pi> x0 = \<pi> c"  
           by (metis (no_types, lifting) IntD1 O_def(1) \<open>c \<in> clusterNodes (Cluster C (local.Suc l)) \<inter> \<pi> k5\<close> thms(6) assms partition_relation)+
         hence "\<pi> k5 = \<pi> x0" by auto
         hence "k5 \<in> \<pi> x0" using in_its_partition[OF assms thms(6)] by auto
         moreover have "k5 \<notin> clusterNodes (Cluster A (Suc l))" using thms(6) clusterNodes_inter_empty by auto
         moreover have "k5 \<notin> X0"  using thms(6) clusterNodes_inter_empty O_def(2) by auto
         ultimately have "k5 = b0" using O_def(5) using thms(6) by auto
         then show ?case using \<open>b0 \<noteq> k5\<close> by auto
       qed
       then obtain a2 where * : "a2 \<in> vertices" "clusterNodes (Cluster A (Suc l)) \<subseteq> \<pi> a2"
         by blast
       then obtain a2 where "a2 \<in> clusterNodes(Cluster A (Suc l))" by auto
       hence a_def: "a2 \<in> clusterNodes(Cluster A (Suc l))" "clusterNodes (Cluster A (Suc l)) \<subseteq> \<pi> a2"
         using assms * unfolding core_def valid_partition_def  
         by (smt (verit, del_insts) UN_iff assms partition_relation subsetD) +
      obtain k2 where k2_def:"k2 \<in> clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster C (Suc l))" "val k2 (\<pi> k2) \<ge> 5/6"
             using cluster_core_min_val[of "Cluster A (Suc l)" "Cluster C (Suc l)", OF _ assms] unfolding f'_def
             by auto
     obtain k3 where k3_def: "k3 \<in> clusterNodes (Cluster A (Suc (Suc l))) \<union> clusterNodes (Cluster C (Suc (Suc l)))" "val k3 (\<pi> k3) \<ge> 5/6"
             using cluster_core_min_val[of "Cluster A (Suc (Suc l))" "Cluster C (Suc (Suc l))", OF _ assms] unfolding f'_def
             by auto
           have C2_ubound:"\<forall>j\<in> clusterNodes (Cluster C (Suc l)). val j (\<pi> j) \<le> 4/5 "
            proof(standard, goal_cases C2)
             case (C2 j)
             show ?case
             proof(cases "j \<in> \<pi> k5", goal_cases j_k5 j_not_k5)
               case j_k5
               have "val j (\<pi> k5) \<le> real 4/ (real 4 + real 1)"
               proof(rule card_val_upper_bound''[of "clusterNodes (Cluster B (pred l)) \<union> clusterNodes (Cluster C  (Suc l))  - {j}" _  "{j}"], goal_cases)
                 case 1
                 then show ?case 
                   using C2 card_Un_disjoint[OF finite_clusterNodes finite_clusterNodes clusterNodes_inter_empty[of "Cluster B (pred l)" "Cluster C (Suc l)"]]
                   clusterCard_correct[symmetric] by auto
               next
                 case 2
                 then show ?case by auto
               next
                 case 3
                 then show ?case by auto
               next
                 case 4
                 have "\<pi> k5 \<subseteq> neighbors k5 \<union> {k5}" using thms(8) by auto
                 hence "\<pi> k5 \<inter> neighbors j \<subseteq>  (neighbors k5 \<union> {k5}) \<inter> neighbors j " by auto
                 moreover have "neighbors j \<inter> neighbors k5 \<subseteq> clusterNodes (Cluster B (pred l)) \<union> clusterNodes (Cluster C (Suc l)) - {j}"
                   using neighbors_intersection[OF C2 thms(6)] no_triangle_cluster_plus[of "Cluster B (pred l)" "Cluster C (Suc l)"] by auto
                 moreover have "j \<noteq> k5" 
                   using C2 thms(6) by auto
                 ultimately show ?case
                   using thms(6) by (auto simp del:clusterNodes.simps)
               next
                 case 5
                 then show ?case using j_k5 no_self_neighbor by auto
               next
                 case 6
                 then show ?case using finite_pi'[OF  assms thms(6)] .
               next
                 case 7
                 then show ?case using finite_clusterNodes by auto
               qed
               moreover have "\<pi> k5 = \<pi> j" using j_k5 
                 by (metis (no_types, lifting) C2 assms partition_relation thms(6))
               ultimately show ?case by auto
             next
               case j_not_k5
               hence j_k5_empty:"\<pi> j \<inter> \<pi> k5 = {}" 
                 using C2 assms equal_or_disjoint example_2.in_its_partition thms(6) by blast
               moreover have "card ( clusterNodes (Cluster  C (Suc l)) \<inter> (\<pi> j \<union> \<pi> k5)) \<le>3"
                 using card_mono 
                 by (metis clusterCard_correct example_2.clusterCard.simps(3) finite_clusterNodes inf_le1)
               ultimately have "card (\<pi> j \<inter> clusterNodes (Cluster  C (Suc l)))\<le> 1" 
                 using card_Un_disjoint[of "clusterNodes (Cluster  C (Suc l)) \<inter> \<pi> j" 
                      "clusterNodes (Cluster  C (Suc l)) \<inter> \<pi> k5"] finite_clusterNodes[of "Cluster C (Suc l)"]
                      C_more_2 clusterCard_correct[of "Cluster  C (Suc l)"]
                 by (smt (verit, ccfv_threshold) finite_Int inf_commute inf_sup_distrib1 inter_empty nat_le_real_less numeral_Bit1 numeral_le_real_of_nat_iff numeral_plus_numeral of_nat_add of_nat_numeral semiring_norm(2))  
               moreover have "j \<in> \<pi> j \<inter> clusterNodes (Cluster  C (Suc l)) " using C2 in_its_partition[OF assms C2] by auto
               moreover then have "card (\<pi> j \<inter> clusterNodes (Cluster  C (Suc l))) \<ge> 1" 
                 using finite_clusterNodes  by (metis One_nat_def Suc_leI card_gt_0_iff empty_iff finite_Int)
               ultimately have * : " (\<pi> j \<inter> clusterNodes (Cluster  C (Suc l))) = {j}" 
                 by (metis card_1_singletonE le_antisym singleton_iff)
               have "val j (\<pi> j) \<le> (real 4)/(real 4 + real 1)"
               proof (rule card_val_upper_bound''[of "clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B (pred l)) - {k5}" _ "{j}"],goal_cases)
                 case 1
                 then show ?case using thms(6) by auto
               next
                 case 2
                 then show ?case by auto
               next
                 case 3
                 then show ?case by auto
               next
                 case 4
                 have " \<pi> j \<inter> neighbors j \<subseteq> clusterNodes (Cluster A (local.Suc l)) \<union> clusterNodes (Cluster C (local.Suc l)) \<union>  clusterNodes (Cluster B (pred l)) - {j}"
                   using  neighbors_correct_set[OF C2] by auto
                 hence " \<pi> j \<inter> neighbors j \<subseteq> clusterNodes (Cluster A (local.Suc l)) \<union>  clusterNodes (Cluster B (pred l))"
                   using * by (auto simp del:clusterNodes.simps)
                 then show ?case using j_k5_empty in_its_partition[OF assms thms(6)] by auto
               next
                 case 5
                 then show ?case using no_self_neighbor  in_its_partition[OF assms C2] by blast
               next
                 case 6
                 then show ?case using finite_pi'[OF assms C2] by blast
               next
                 case 7
                 then show ?case using finite_clusterNodes by auto
               qed
               then show ?case by auto
             qed
           qed
           hence k2_def:"k2 \<in> clusterNodes (Cluster A (Suc l))" "val k2 (\<pi> k2) \<ge> 5/6" using k2_def by fastforce+
have card_1:"card (clusterNodes (Cluster A l) - X) = 1" 
           by (metis card_Diff_subset clusterCard_correct diff_add_inverse example_2.clusterCard.simps(1) finite_clusterNodes finite_subset nat_1_add_1 numeral_Bit1 numerals(1) thms(2) thms(5))
       have "\<pi> k1 \<inter> clusterNodes (Cluster A l) = {} \<or> \<pi> k5 \<inter> clusterNodes (Cluster A l) = {}"
       proof (rule ccontr,goal_cases asm)
         case asm
         then obtain a1 where a1_def: "a1 \<in> \<pi> k1"  " a1\<in> clusterNodes (Cluster A l)" 
            by auto
         moreover have "\<pi> k1 \<inter> \<pi> x' = {}" 
           by (smt (verit, ccfv_SIG) assms card_not_2 equal_or_disjoint example_2.Suc.elims example_2.pred.simps(1) example_2.pred.simps(2) example_2.pred.simps(3) example_2.pred.simps(4) example_2.pred.simps(5) inters(1) thms(1) thms(11) thms(5) thms(9)) 
         hence "\<pi> k1 \<inter> X = {}" 
           using inters(1) by blast
         ultimately have * :"clusterNodes (Cluster A l) - X = {a1}" 
           using card_1 by (smt (verit) DiffI card_1_singletonE disjoint_iff singletonD)
         from asm obtain a5 where a5_def: "a5 \<in> \<pi> k5"  " a5\<in> clusterNodes (Cluster A l)" 
           by auto
         moreover have "\<pi> k5 \<inter> \<pi> x' = {}"
           by (smt (verit, best) assms card_not_2 equal_or_disjoint example_2.pred.elims example_2.pred.simps(1) example_2.pred.simps(2) example_2.pred.simps(3) example_2.pred.simps(4) example_2.pred.simps(5) inters(1) thms(1) thms(5) thms(6) thms(8))
         hence "\<pi> k5 \<inter> X = {}" 
           using inters(1) by blast
         ultimately have "clusterNodes (Cluster A l) - X = {a5}" using card_1 
           by (smt (verit) DiffI card_1_singletonE disjoint_iff singletonD)
         hence "a1 = a5" using * by auto
         then show ?case using a1_def(1) a5_def(1) k1_k5_disjoint by auto
       qed          
       thus False
       proof (standard, goal_cases A1 A5)
         case A1
           have "clusterNodes (Cluster A (Suc l)) \<subseteq> \<pi> k1"
         proof (rule ccontr, goal_cases asm)
           case asm
           have  "\<pi> k1  \<inter>  clusterNodes (Cluster A l ) ={}" using A1 by auto
           moreover from asm have "\<pi> k1 \<noteq> \<pi> a2 "  using a_def(2) by blast
           hence "\<pi> k1 \<inter> \<pi> a2 = {}" using a_def(1) assms equal_or_disjoint thms(9) by blast
           hence "\<pi> k1 \<inter> clusterNodes (Cluster A (Suc l)) = {}" using a_def by auto
           moreover have "\<pi> k1 \<subseteq> neighbors k1 \<union> {k1}" using  thms(11) by auto
           moreover have " neighbors k1 \<union> {k1} = \<Union> (clusterNodes ` neighboring_clusters (Cluster B l)) " 
             by (smt (verit) UN_iff Un_Diff_cancel2 Un_commute in_neighboring insert_absorb insert_is_Un neighbors_correct_set thms(9))
           ultimately have **: "\<pi> k1 \<subseteq> clusterNodes (Cluster B l ) \<union> clusterNodes (Cluster C (Suc (Suc l)))"
             by (auto simp del:clusterNodes.simps)
           moreover have *:"card (\<pi> k1 \<inter> neighbors k1) \<ge> 4"
             using card_val_lower_bound[OF finite_pi'[OF assms thms(9)]] unfolding f'_def
             using thms(10) thms(9)
             by (metis (no_types, lifting) assms in_its_partition numeral_Bit1 numeral_code(2) of_nat_numeral)
           have "k1 \<in> \<pi> k1 - neighbors k1" 
             by (metis (no_types, lifting) DiffI assms in_its_partition no_self_neighbor thms(9))
           hence "card (\<pi> k1 - neighbors k1) \<ge> 1" 
             by (metis (no_types, lifting) One_nat_def Suc_leI assms card_gt_0_iff empty_iff finite_Diff finite_pi' thms(9))
           hence "card (\<pi> k1) \<ge> 5" using * 
                card_Un_disjoint[of "\<pi> k1 \<inter> neighbors k1" "\<pi> k1 - neighbors k1"] finite_pi'[OF assms thms(9)] finite_subset 
             by (smt (verit) Int_Diff_Un Int_Diff_disjoint finite_Diff finite_Int nat_le_real_less numeral_Bit1 numeral_code(2) numeral_le_real_of_nat_iff of_nat_add of_nat_numeral)
           hence "card (\<pi> k1) = 5" using calculation card_mono[OF _ calculation] finite_clusterNodes by auto
           ultimately have pi_k1:"\<pi> k1 = clusterNodes (Cluster B l ) \<union> clusterNodes (Cluster C (Suc (Suc l)))" 
             using card_subset_eq[OF _ **] finite_clusterNodes by auto
           have "\<exists>a3\<in> vertices. clusterNodes (Cluster A (Suc (Suc l))) \<subseteq> \<pi> a3"
           proof (rule ccontr, goal_cases asm)
             case asm
             then obtain x0 X0 b0 
                where O_def: "x0 \<in> clusterNodes (Cluster C (Suc (Suc l)))"
          "X0 \<subseteq> clusterNodes (Cluster A (Suc (Suc l)))" "b0 \<in> clusterNodes (Cluster B l)"
          "card X0 = 2"  "\<pi> x0 = clusterNodes (Cluster C (Suc (Suc l))) \<union> X0 \<union> {b0}"
               using A_superplayer_aux[OF assms]   by (metis (no_types, lifting) pred_suc)
             obtain c where "c \<in> clusterNodes (Cluster C (Suc (Suc l)))" by auto
             hence "c \<in> \<pi> x0" " c\<in> \<pi> k1" using pi_k1 O_def(5) by auto
             hence eq:"\<pi> x0 = \<pi> k1" 
               by (meson O_def(1) assms disjoint_iff equal_or_disjoint thms(9))
             have "\<pi> k1 \<inter> clusterNodes (Cluster B l ) = clusterNodes (Cluster B l )" using pi_k1
               by blast
             moreover have "\<pi> x0 \<inter> clusterNodes (Cluster B l) = {b0}" 
               using O_def clusterNodes_inter_empty by auto
             ultimately have "\<pi> x0 \<noteq> \<pi> k1"
               by (metis card_2_iff' clusterCard_correct example_2.clusterCard.simps(2) singletonD)
             then show ?case using eq by auto
           qed
           have C3_ubound:"\<forall>j\<in>clusterNodes (Cluster C (Suc (Suc l))). val j (\<pi> j) = 4/5"
           proof (standard,goal_cases C3)
             case (C3 j)
             hence "j \<in> \<pi> k1" 
               using pi_k1 by auto
             hence "\<pi> j = \<pi> k1" 
               by (meson C3 assms partition_relation thms(9))
             moreover have "\<pi> k1 \<inter> neighbors j = clusterNodes (Cluster B l) \<union> clusterNodes (Cluster C (Suc (Suc l))) - {j}"
               using pi_k1 neighbors_correct_set[OF C3] by auto
             moreover have "card(...) = 4 " using C3 by auto
             moreover have "card(\<pi> k1) = 5" using pi_k1 by auto
             ultimately show ?case using val_graph_correct[OF finite_pi'[OF assms thms(9)],of j] unfolding val_graph_def
               by auto
           qed
           have "card (\<pi> k2 \<inter> neighbors k2) \<ge> 5" using k2_def card_val_lower_bound[OF finite_pi'[OF assms k2_def(1)]] unfolding f'_def 
             by (smt (verit, ccfv_threshold) assms in_its_partition numeral_Bit1 of_nat_1 of_nat_add one_add_one)
           have "k2 \<notin> \<pi> k1" using pi_k1 k2_def(1) clusterNodes_inter_empty by auto
           hence "\<pi> k2 \<inter> \<pi> k1 = {}" using assms k2_def thms(9) unfolding core_def valid_partition_def
             by (meson assms partition_relation)
           hence k2_B1:"\<pi> k2 \<inter> clusterNodes (Cluster B l) = {}" using thms(9) pi_k1 by auto
           have "k2 \<noteq> k5"   "k2 \<notin>  neighbors k5"
             using k2_def(1) thms(6) apply  force
              using neighbor_check[OF k2_def(1) thms(6)]  by (metis example_2.clusterEdge.simps(4) pred_suc_diff suc_diff suc_pred)
            hence "k2 \<notin> \<pi> k5" using thms(8) by auto
            hence "\<pi> k2 \<inter> \<pi> k5 = {}" 
              by (meson assms k2_def(1) partition_relation thms(6))
                moreover have "card ( clusterNodes (Cluster  C (Suc l)) \<inter> (\<pi> k2 \<union> \<pi> k5)) \<le>3"
                 using card_mono 
                 by (metis clusterCard_correct example_2.clusterCard.simps(3) finite_clusterNodes inf_le1)
               ultimately have k2_C2: "card (\<pi> k2 \<inter> clusterNodes (Cluster  C (Suc l)))\<le> 1" 
                 using card_Un_disjoint[of "clusterNodes (Cluster  C (Suc l)) \<inter> \<pi> k2" 
                      "clusterNodes (Cluster  C (Suc l)) \<inter> \<pi> k5"] finite_clusterNodes[of "Cluster C (Suc l)"]
                      C_more_2 clusterCard_correct[of "Cluster  C (Suc l)"]
                 by (smt (verit, ccfv_threshold) finite_Int inf_commute inf_sup_distrib1 inter_empty nat_le_real_less numeral_Bit1 numeral_le_real_of_nat_iff numeral_plus_numeral of_nat_add of_nat_numeral semiring_norm(2))  
               have "\<pi> k2 \<inter>  \<Union> (clusterNodes ` (neighboring_clusters (Cluster A (Suc l) ))) \<subseteq>
                    (\<pi> k2 \<inter> clusterNodes (Cluster  C (Suc l))) \<union> clusterNodes (Cluster A (Suc l))
                    \<union> clusterNodes (Cluster B (Suc l))   
" using  k2_B1  
                 by (auto simp del:clusterNodes.simps simp add: boolean_algebra.conj_disj_distrib clusterNodes_inter_empty)
               hence "\<pi> k2 \<inter> neighbors k2 \<subseteq> (\<pi> k2 \<inter> clusterNodes (Cluster  C (Suc l))) \<union> clusterNodes (Cluster A (Suc l))
                    \<union> clusterNodes (Cluster B (Suc l)) - {k2}" using neighbors_correct_set[OF k2_def(1)]  by (auto simp del:clusterNodes.simps) 
               moreover have "card ((\<pi> k2 \<inter> clusterNodes (Cluster  C (Suc l))) \<union> clusterNodes (Cluster A (Suc l)))
                  \<le> 4"
                 using k2_C2 card_Un_le[of "\<pi> k2 \<inter> clusterNodes (Cluster  C (Suc l))" "clusterNodes (Cluster A (Suc l))"] clusterCard_correct by auto
               hence "card ( (\<pi> k2 \<inter> clusterNodes (Cluster  C (Suc l))) \<union> clusterNodes (Cluster A (Suc l))
                    \<union> clusterNodes (Cluster B (Suc l))) \<le> 6" 
                 using card_Un_le by auto
               hence "card ((\<pi> k2 \<inter> clusterNodes (Cluster  C (Suc l))) \<union> clusterNodes (Cluster A (Suc l))
                    \<union> clusterNodes (Cluster B (Suc l)) - {k2})\<le>5" using k2_def(1) by auto
               ultimately have "card(\<pi> k2 \<inter> neighbors k2) \<le> 5 " using card_mono finite_clusterNodes finite_subset 
                 by (smt (verit, best) finite_Diff finite_Int finite_UnI le_trans)
               hence *:"card (\<pi> k2 \<inter> neighbors k2) = 5" 
                 using \<open>5 \<le> card (\<pi> k2 \<inter> neighbors k2)\<close> nle_le by blast
               moreover then  have "card ((\<pi> k2 \<inter> clusterNodes (Cluster  C (Suc l))) \<union> clusterNodes (Cluster A (Suc l))
                    \<union> clusterNodes (Cluster B (Suc l)) - {k2}) = 5" 
                 by (metis (no_types, lifting) \<open>\<pi> k2 \<inter> neighbors k2 \<subseteq> \<pi> k2 \<inter> clusterNodes (Cluster C (local.Suc l)) \<union> clusterNodes (Cluster A (local.Suc l)) \<union> clusterNodes (Cluster B (local.Suc l)) - {k2}\<close> \<open>card (\<pi> k2 \<inter> clusterNodes (Cluster C (local.Suc l)) \<union> clusterNodes (Cluster A (local.Suc l)) \<union> clusterNodes (Cluster B (local.Suc l)) - {k2}) \<le> 5\<close> card_mono finite_Diff finite_Int finite_UnI finite_clusterNodes le_antisym)
               ultimately have pi_k2_neighbors:"\<pi> k2 \<inter> neighbors k2 = (\<pi> k2 \<inter> clusterNodes (Cluster  C (Suc l))) \<union> clusterNodes (Cluster A (Suc l))
                    \<union> clusterNodes (Cluster B (Suc l)) - {k2} " 
                 by (metis (no_types, lifting) \<open>\<pi> k2 \<inter> neighbors k2 \<subseteq> \<pi> k2 \<inter> clusterNodes (Cluster C (local.Suc l)) \<union> clusterNodes (Cluster A (local.Suc l)) \<union> clusterNodes (Cluster B (local.Suc l)) - {k2}\<close> card_subset_eq finite_Diff finite_Int finite_UnI finite_clusterNodes)
               have "card (\<pi> k2) \<le> real 6" using * val_graph_correct[OF finite_pi'[OF assms k2_def(1)], of k2]  k2_def(2)  unfolding val_graph_def
                 by (metis frac_less2 linorder_not_le nle_le not_numeral_le_zero of_nat_numeral)
               hence "card (\<pi> k2) \<le> 6" by auto
               hence "card (\<pi> k2 - neighbors k2) \<le> 1" using * card_Un_disjoint[of "\<pi> k2 \<inter> neighbors k2" "\<pi> k2 - neighbors k2" ] finite_pi'[OF assms k2_def(1)] 
                 by (smt (verit, ccfv_SIG) Int_Diff_Un Int_Diff_disjoint finite_Diff finite_Int nat_le_real_less numeral_Bit0 numeral_Bit1 of_nat_add)
               moreover have "{k2} \<subseteq> \<pi> k2 - neighbors k2 " using in_its_partition[OF assms k2_def(1)] no_self_neighbor by auto
               ultimately have "\<pi> k2 - neighbors k2 = {k2}" using card_mono[of "\<pi> k2 - neighbors k2" "{k2}"] card_subset_eq[of "\<pi> k2 - neighbors k2" "{k2}"]  
                 by (metis (no_types, lifting) One_nat_def assms card.empty card_insert_if empty_iff finite.emptyI finite_Diff finite_pi' k2_def(1) le_antisym)
               hence pi_k2_def:"\<pi> k2 = (\<pi> k2 \<inter> clusterNodes (Cluster  C (Suc l))) \<union> clusterNodes (Cluster A (Suc l))
                    \<union> clusterNodes (Cluster B (Suc l)) " using pi_k2_neighbors k2_def 
                 by (smt (verit, best) Int_Diff_Un UnI1 Un_Diff_cancel insert_absorb insert_is_Un sup_commute)
               have k3_def:"k3 \<in> clusterNodes (Cluster A (Suc (Suc l)))" "val k3 (\<pi> k3) \<ge> 5/6" using k3_def C3_ubound by fastforce+
               hence * :"card (\<pi> k3 \<inter> neighbors k3) \<ge> 5" using card_val_lower_bound[OF finite_pi'[OF assms k3_def(1)]] unfolding f'_def 
                 by (smt (verit, ccfv_threshold) assms in_its_partition numeral_Bit1 of_nat_1 of_nat_add one_add_one)
               have "\<pi> k2 \<subseteq> clusterNodes (Cluster  C (Suc l)) \<union> clusterNodes (Cluster A (Suc l))
                    \<union> clusterNodes (Cluster B (Suc l))" using pi_k2_def by blast
               hence "k3 \<notin> \<pi> k2" using k3_def(1) clusterNodes_inter_empty  by auto
               hence "\<pi> k3 \<inter> \<pi> k2 = {}" 
                 by (meson assms k2_def(1) k3_def(1) partition_relation)
               hence "\<pi> k3 \<inter>  clusterNodes (Cluster B (Suc l)) = {}" using pi_k2_def by auto
               moreover have "k3 \<notin> \<pi> k1" using k3_def(1) pi_k1 clusterNodes_inter_empty by auto
               hence "\<pi> k3 \<inter> \<pi> k1 = {}" 
                 by (meson assms k3_def(1) partition_relation thms(9))
               hence "\<pi> k3 \<inter> clusterNodes (Cluster C (Suc (Suc l))) = {}" using pi_k1 by auto
               ultimately have "\<pi> k3 \<inter> neighbors k3 \<subseteq> clusterNodes (Cluster A (Suc (Suc l))) \<union> clusterNodes (Cluster B (Suc (Suc l))) - {k3}"
                 using neighbors_correct_set[OF k3_def(1)] by auto
               moreover have "card (clusterNodes (Cluster A (Suc (Suc l))) \<union> clusterNodes (Cluster B (Suc (Suc l))) - {k3}) = 4"
                 using k3_def(1) card_Un_disjoint[OF finite_clusterNodes finite_clusterNodes clusterNodes_inter_empty] by auto
               ultimately have "card (\<pi> k3 \<inter> neighbors k3) \<le> 4" using card_mono 
                 by (metis (no_types, lifting) finite_Diff finite_UnI finite_clusterNodes)
                then show ?case using * by auto
              qed
              hence pi_k1_k2:"\<pi> k2 = \<pi> k1" using k2_def(1) assms thms(9) unfolding core_def valid_partition_def
                by blast
              moreover have "card (\<pi> k2 \<inter> neighbors k2) \<ge> 5" using card_val_lower_bound k2_def(2) finite_pi'[OF assms k2_def(1)]
                    in_its_partition[OF assms k2_def(1)] unfolding f'_def by auto
              ultimately have "card (\<pi> k1 \<inter> neighbors k2)\<ge> 5" by auto
              moreover have "\<pi> k1 \<inter> neighbors k2 \<subseteq>  neighbors k2 \<inter> ( neighbors k1 \<union> {k1})"
                using thms(11) by auto
              moreover have "neighbors k2 \<inter> neighbors k1 \<subseteq> (clusterNodes (Cluster A (Suc l))
                     \<union> clusterNodes (Cluster B l))"
                using neighbors_intersection[OF k2_def(1) thms(9)] thms(9) pred_suc suc_pred 
                by auto
              hence "neighbors k2 \<inter> (neighbors k1 \<union> {k1}) \<subseteq>  clusterNodes (Cluster A (Suc l))
                     \<union> clusterNodes (Cluster B l)"
                using thms(9) by auto
              moreover have "card (clusterNodes (Cluster A (Suc l))
                     \<union> clusterNodes (Cluster B l)) = 5" by auto
              ultimately have "\<pi> k1 \<inter> neighbors k2 = clusterNodes (Cluster A (Suc l))
                     \<union> clusterNodes (Cluster B l) "
                by (smt (verit, ccfv_SIG) card_mono card_subset_eq finite_UnI finite_clusterNodes nle_le subset_trans)
              hence "k2 \<in> neighbors k2" using k2_def(1) by auto
              thus False using no_self_neighbor by auto
       next
         case A5
         have pi_k5_def:"\<pi> k5 = clusterNodes (Cluster B (pred l)) \<union> clusterNodes (Cluster C (Suc l))"
         proof -
           have "\<pi> k5 \<inter> \<pi> k = {}" 
             using k_k5_not_co partition_relation[OF assms k_def'(1) thms(6)] by auto
           hence "\<pi> k5 \<inter> clusterNodes(Cluster A (pred l)) = {}" using A5_pi_k by auto
           hence  *:"\<pi> k5 \<inter> neighbors k5 \<subseteq> clusterNodes (Cluster B (pred l)) \<union> clusterNodes (Cluster C (Suc l)) - {k5}"
             using neighbors_correct_set[OF thms(6)] A5 by auto
           moreover have **:"card (clusterNodes (Cluster B (pred l)) \<union> clusterNodes (Cluster C (Suc l)) - {k5}) = 4"
             using thms(6) by auto
           ultimately have ***:"card (\<pi> k5 \<inter> neighbors k5) \<le>4" 
             by (metis (no_types, lifting) card_mono finite_Diff finite_UnI finite_clusterNodes)
           moreover have ****: "card (\<pi> k5 \<inter> neighbors k5) \<ge> 4" using card_val_lower_bound[OF finite_pi'[OF assms thms(6)] _ in_its_partition[OF assms thms(6)] ]
             thms(7) unfolding f'_def by auto
           ultimately have pi_k5_neighbors:"\<pi> k5 \<inter> neighbors k5 = clusterNodes (Cluster B (pred l)) \<union> clusterNodes (Cluster C (Suc l)) - {k5}" using * ** 
             by (metis (no_types, lifting) card_subset_eq finite_Diff finite_UnI finite_clusterNodes le_antisym)
           have "card (\<pi> k5 \<inter> neighbors k5) = 4" using *** **** by auto 
           moreover then have "card(\<pi> k5) \<le> 5" using thms(7) val_graph_correct[OF finite_pi'[OF assms thms(6)], of k5] unfolding val_graph_def 
             by (smt (verit, ccfv_SIG) frac_less2 of_nat_le_0_iff of_nat_le_iff zero_neq_numeral)
           ultimately have "card (\<pi> k5 - neighbors k5) \<le> 1" using card_Un_disjoint[of "\<pi> k5 \<inter> neighbors k5" "\<pi> k5 - neighbors k5" ] finite_pi'[OF assms thms(6)] 
             by (simp add: Int_Diff_Un Int_Diff_disjoint)
           moreover have "{k5} \<subseteq> \<pi> k5 - neighbors k5 " using in_its_partition[OF assms thms(6)] no_self_neighbor by blast
           ultimately have "\<pi> k5 - neighbors k5 = {k5}"
             by (smt (verit) Diff_eq_empty_iff Diff_insert Diff_insert2 subset_antisym thms(8))
           then show ?thesis using pi_k5_neighbors using thms(6)
             by (metis (no_types, lifting) IntE Int_Diff_Un Un_Int_eq(3) insert_Diff insert_is_Un sup_commute)
         qed
         have "\<forall>j \<in> clusterNodes (Cluster C (Suc l)). val j (\<pi> j) = 4/5"
         proof(standard,goal_cases C2)
           case (C2 j)
           hence eq_j_k5:"\<pi> j = \<pi> k5" using partition_relation[OF assms C2 thms(6)] pi_k5_def 
             by (metis UnCI)
           hence "\<pi> j \<inter> neighbors j = \<pi> k5 - {j}" using neighbors_correct_set[OF C2] unfolding pi_k5_def by auto
           moreover have "card ( \<pi> k5 - {j}) = 4" unfolding pi_k5_def using C2 by auto
           ultimately have "card (\<pi> j \<inter> neighbors j) = 4" by auto
           moreover have "\<pi> j - neighbors j = {j}" using neighbors_correct_set[OF C2] in_its_partition[OF assms C2] no_self_neighbor[of j] 
             unfolding pi_k5_def  eq_j_k5 by auto
           hence "card (\<pi> j - neighbors j) = 1" by auto
           hence "card(\<pi> j) = 5" using calculation finite_pi'[OF assms C2] card_Un_disjoint[of "\<pi> j \<inter> neighbors j" "\<pi> j - neighbors j"]
            finite_subset
             by (simp add: Int_Diff_Un Int_Diff_disjoint)
           ultimately show ?case using val_graph_correct[OF finite_pi'[OF assms C2]] unfolding val_graph_def
             by (metis of_nat_numeral)
         qed
          have  card_k2:"card (\<pi> k2 \<inter> neighbors k2) \<ge> 5" 
             using card_val_lower_bound[OF finite_pi'[OF assms k2_def(1)] _ in_its_partition[OF assms k2_def(1)]] 
             unfolding f'_def using k2_def  by auto
         have k1_k2:"k1 \<notin> \<pi> k2"
         proof(rule ccontr,goal_cases asm)
           case asm
           hence "\<pi> k2 = \<pi> k1" using partition_relation[OF assms  thms(9) k2_def(1)] by auto
           hence "\<pi> k2 \<inter> neighbors k2 \<subseteq> neighbors k2 \<inter> (neighbors k1 \<union> {k1})" 
             using thms(11) by auto
           moreover have "... \<subseteq> (clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B l) - {k2}) \<union> {k1}"
             using neighbors_intersection[OF k2_def(1) thms(9)] no_triangle_cluster_plus[of "Cluster B l" "Cluster A (Suc l)" ]
             by (auto simp del:clusterNodes.simps)
           moreover have "... \<subseteq> clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B l) - {k2} " 
               using thms(9) k2_def(1) by auto
           moreover have "card (clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B l) - {k2}) = 4"
               using k2_def(1) by auto
           ultimately have "card (\<pi> k2 \<inter> neighbors k2) \<le> 4" 
             by (smt (verit) card_mono finite_Diff finite_UnI finite_clusterNodes subset_trans)
           thus ?case using card_k2 by auto
          qed
          moreover have "k2 \<notin> \<pi> k5" using k2_def(1) pi_k5_def clusterNodes_inter_empty by auto
          hence "\<pi> k2 \<inter> \<pi> k5 = {}" using partition_relation[OF assms k2_def(1) thms(6)] by auto
          hence "\<pi> k2 \<inter> clusterNodes (Cluster C (Suc l)) = {}" using pi_k5_def by auto
          ultimately have * :"\<pi> k2 \<inter> neighbors k2 \<subseteq> clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B (Suc l)) \<union>
 clusterNodes (Cluster B l) - {k1,k2}" using neighbors_correct_set[OF k2_def(1)] by auto
          have "card (clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B (Suc l))) = 5" by auto
          hence " card (clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B (Suc l)) \<union> clusterNodes (Cluster B l)) = 7"
            using
              card_Un_disjoint[of "clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B (Suc l))" "clusterNodes (Cluster B l)" ]
            by auto
          moreover have " k1 \<in> clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B (Suc l)) \<union> clusterNodes (Cluster B l) "
            " k2 \<in> clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B (Suc l)) \<union> clusterNodes (Cluster B l) "
            "k1 \<noteq> k2"    using thms(9) k2_def(1) by auto
          ultimately have  **: "card((clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B (Suc l)) \<union>
 clusterNodes (Cluster B l)) - {k1,k2}) = 5" by auto
          with * card_k2 have card_k2:"card (\<pi> k2 \<inter> neighbors k2) = 5" 
            by (smt (verit, del_insts) card_mono finite_Diff finite_UnI finite_clusterNodes le_antisym)
          with * ** have pi_k2_neighbors: "\<pi> k2 \<inter> neighbors k2 = clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B (Suc l)) \<union>
 clusterNodes (Cluster B l) - {k1,k2}" 
            by (metis (no_types, lifting) ** card_subset_eq finite_Diff finite_UnI finite_clusterNodes)
          from card_k2 have "card(\<pi> k2) \<le> 6" using val_graph_correct[OF finite_pi'[OF assms k2_def(1)], of k2] unfolding val_graph_def
            using k2_def(2) 
            by (smt (verit, best) frac_less2 nat_le_real_less numeral_Bit0 numeral_Bit1 of_nat_1 of_nat_add one_add_one)
          hence "card (\<pi> k2 - neighbors k2) \<le> 1" using card_k2 card_Un_disjoint[of "\<pi> k2 \<inter> neighbors k2"
                    "\<pi> k2 - neighbors k2"]  
            by (metis (no_types, lifting) Int_Diff_Un Int_Diff_disjoint assms finite_Diff finite_Int finite_pi' k2_def(1) nat_add_left_cancel_le one_plus_numeral one_plus_numeral_commute semiring_norm(4) semiring_norm(5))
          moreover have "{k2} \<subseteq>\<pi> k2 - neighbors k2" using in_its_partition[OF assms k2_def(1)] no_self_neighbor by auto
          ultimately have "\<pi> k2 - neighbors k2 = {k2}" 
            by (metis (no_types, lifting) One_nat_def assms card.empty card_insert_if card_seteq empty_iff finite.emptyI finite_Diff finite_pi' k2_def(1))
          with  pi_k2_neighbors have "\<pi> k2 = clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B (Suc l)) \<union>
 clusterNodes (Cluster B l) - {k1} \<union> {k2}"  by (auto simp del:clusterNodes.simps)
          hence pi_k2:"\<pi> k2 = clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster B (Suc l)) \<union>
 clusterNodes (Cluster B l) - {k1}" using k2_def(1) \<open>k1 \<noteq> k2\<close> by blast
          obtain a1 where  a1_def: "clusterNodes (Cluster A l) - X = {a1}" "a1 \<in> clusterNodes (Cluster A l) " using card_1 
            using card_1_singletonE by blast
          obtain b1 where b1_def: "clusterNodes(Cluster B l) - {k1} = {b1}" using thms(9)
            apply auto 
            by (metis Diff_insert_absorb One_nat_def Suc_1 example_2.Node.inject insert_commute n_not_Suc_n singletonD)
          have "k1 \<notin> \<pi> x'" using thms(1,2,3,4,9) 
            by (smt (verit, ccfv_SIG) assms card_not_2 example_2.ClusterNumber.exhaust example_2.pred.simps(1) example_2.pred.simps(2) example_2.pred.simps(3) example_2.pred.simps(4) example_2.pred.simps(5) inters(1) partition_relation thms(11) thms(5))
          hence "\<pi> k1 \<inter> \<pi> x' = {}" using partition_relation[OF assms thms(9) thms(1)] by auto
          hence "\<pi> k1 \<inter> X = {}" using inters(1) by auto
          hence "\<pi> k1 \<inter> clusterNodes (Cluster A l) \<subseteq> {a1}" using a1_def by auto
          moreover have "\<pi> k1 \<inter> \<pi> k2 = {}" using k1_k2 partition_relation[OF assms thms(9) k2_def(1)] by auto
          hence "\<pi> k1 \<inter> (clusterNodes (Cluster B l) \<union> clusterNodes (Cluster A (Suc l))) \<subseteq> 
                 {k1} "
             unfolding pi_k2 by (auto simp del:clusterNodes.simps) 
           ultimately have * :"\<pi> k1 \<inter> neighbors k1 \<subseteq> clusterNodes (Cluster C (Suc (Suc l))) \<union> {a1}"
             using neighbors_correct_set[OF thms(9)] by (auto simp del:clusterNodes.simps)
           moreover have "a1 \<notin> clusterNodes (Cluster C (Suc (Suc l)))" 
             using clusterNodes_inter_empty[of "Cluster C (Suc (Suc l))" "Cluster A l"]
                a1_def by blast
           hence ** :"card(clusterNodes (Cluster C (Suc (Suc l))) \<union> {a1}) = 4" by auto               
           moreover have "card (\<pi> k1 \<inter> neighbors k1) \<ge> 4 " using 
          card_val_lower_bound[OF finite_pi'[OF assms thms(9)] _ in_its_partition[OF assms thms(9)] ] unfolding f'_def using 
             thms(10) by auto
           ultimately have card_pi_k1_neighbors:"card (\<pi> k1 \<inter> neighbors k1) = 4" using card_mono finite_clusterNodes 
             by (smt (verit, best) a1_def finite_Diff finite_UnI le_antisym)
           hence pi_k1_neighbors: "\<pi> k1 \<inter> neighbors k1 =  clusterNodes (Cluster C (Suc (Suc l))) \<union> {a1}"
             using * ** 
             by (simp add: card_subset_eq)
           have "card (\<pi> k1) \<le> 5" using thms(10) 
              card_pi_k1_neighbors
             unfolding val_graph_correct[OF finite_pi'[OF assms thms(9)],of k1, symmetric] val_graph_def
             by (smt (verit, best) frac_less2 of_nat_le_0_iff of_nat_le_iff zero_neq_numeral)
           hence "card (\<pi> k1 - neighbors k1) \<le> 1" using card_pi_k1_neighbors card_Un_disjoint[of "\<pi> k1 \<inter> neighbors k1"
"\<pi> k1 - neighbors k1"] finite_pi'[OF assms thms(9)] finite_subset 
             by (smt (verit) Int_Diff_Un Int_Diff_disjoint finite_Diff finite_Int nat_le_real_less numeral_Bit1 numeral_code(2) of_nat_add)
          moreover have "{k1} \<subseteq> \<pi> k1 - neighbors k1 " using in_its_partition[OF assms thms(9)] no_self_neighbor by blast
          ultimately have " \<pi> k1 - neighbors k1 = {k1}"  using thms(11) by fastforce
          hence pi_k1:"\<pi> k1 =  clusterNodes (Cluster C (Suc (Suc l))) \<union> {a1,k1} " using pi_k1_neighbors by blast
          have "\<forall>j\<in>clusterNodes (Cluster C (Suc (Suc l))). val j (\<pi> j) \<le> real 3/ (real 3 + real 1)"
          proof (standard, goal_cases C3)
            case (C3 j)
            have  "val j (\<pi> k1) \<le> real 3/ (real 3 + real 1)"
            proof (rule card_val_upper_bound''[of "(clusterNodes (Cluster C (Suc (Suc l))) - {j}) \<union> {k1}" _ "{j}" ], goal_cases)
              case 1
              then show ?case using thms(9) clusterNodes_inter_empty C3 by auto
            next
              case 2
              then show ?case by auto
            next
              case 3
              then show ?case by auto
            next
              case 4
               have "k1 \<in> neighbors j" 
              using  neighbor_check[OF thms(9) C3] C3 clusterNodes_inter_empty[of "Cluster A l" "Cluster C (Suc (Suc l))"] 
              using thms(9) by auto
              moreover have  "clusterNodes (Cluster C (Suc (Suc l))) -{j} \<subseteq> neighbors j"
                using neighbors_correct_set[OF C3] C3 clusterNodes_inter_empty  by auto
              moreover have "a1 \<notin> neighbors j" 
                using neighbor_check[OF a1_def(2) C3] by auto
              moreover have "j \<notin> neighbors j" using no_self_neighbor by blast
              ultimately show ?case unfolding pi_k1  by auto
            next
              case 5
              then show ?case using C3 pi_k1 no_self_neighbor by auto
            next
              case 6
              then show ?case using finite_pi'[OF assms thms(9)] .
            next
              case 7
              then show ?case using finite_clusterNodes by auto
            qed
            moreover have "\<pi> j = \<pi> k1" using pi_k1 partition_relation[OF assms C3 thms(9)] C3 by auto
            ultimately show ?case by auto
          qed
          hence k3_def: "k3 \<in> clusterNodes (Cluster A (Suc (Suc l)))" "val k3 (\<pi> k3) \<ge> 5/6 "
              using k3_def by auto
            hence "k3 \<notin> neighbors k1"  "k3 \<noteq> k1" using thms(9) neighbor_check[OF k3_def(1) thms(9)]
              apply (smt (verit) ClusterNumber.distinct(18) example_2.Suc.elims example_2.clusterEdge.simps(4) example_2.pred.simps(1) example_2.pred.simps(2) example_2.pred.simps(3) example_2.pred.simps(4) example_2.pred.simps(5))
              using k3_def(1) thms(9) by auto
            hence "k3 \<notin> \<pi> k1" using thms(11) by auto
            hence "\<pi> k3 \<inter> \<pi> k1 = {}" using partition_relation[OF assms k3_def(1) thms(9)] by auto
            hence "\<pi> k3 \<inter> clusterNodes (Cluster C (Suc (Suc l))) = {}" using pi_k1 by auto
            moreover have "k3 \<notin> \<pi> k2" using pi_k2 k3_def(1) clusterNodes_inter_empty by fastforce
            hence "\<pi> k3 \<inter> \<pi> k2 = {}" using partition_relation[OF assms k3_def(1) k2_def(1)] by auto
            hence "\<pi> k3 \<inter> clusterNodes (Cluster B (Suc l)) = {}" using pi_k2 thms(9) clusterNodes_inter_empty by fastforce
            ultimately have "\<pi> k3 \<inter> neighbors k3 \<subseteq> clusterNodes (Cluster A (Suc (Suc l))) \<union>  clusterNodes (Cluster B (Suc (Suc l))) - {k3}"
              unfolding neighbors_correct_set[OF k3_def(1)] by auto
            moreover have "card(...)\<le> 4" using k3_def(1) by auto
            ultimately have "card(\<pi> k3 \<inter> neighbors k3)\<le> 4" 
              using card_mono[OF finite_subset[OF _ finite_pi'[OF assms k3_def(1)]]] 
              by (meson card_mono finite_Diff finite_UnI finite_clusterNodes le_trans)
            moreover have "card (\<pi> k3 \<inter> neighbors k3)\<ge>5" using card_val_lower_bound[OF finite_pi'[OF assms k3_def(1)] _ in_its_partition[OF assms k3_def(1)]] unfolding f'_def using k3_def(2)
              by auto
            ultimately show False by auto
          qed
        qed

lemma C_superplayer_aux:
  fixes l \<pi>
  assumes "\<pi> \<in> core"
  shows "\<exists>i\<in> clusterNodes (Cluster C l). val i (\<pi> i) \<ge> 4/5"
proof (rule ccontr, goal_cases C1_ubound)
  case C1_ubound
  obtain i where "i \<in> clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l)))"
      "val i (\<pi> i)\<ge> 4/5"
    using cluster_core_min_val[OF _ assms, of "Cluster C l" "Cluster B (pred (pred l))" ] 
    unfolding f'_def by auto
  hence i_def: "i \<in> clusterNodes (Cluster B (pred (pred l)))" "val i (\<pi> i)\<ge> 4/5" using C1_ubound by auto
  then obtain i where i_def: "i \<in> clusterNodes (Cluster B (pred (pred l)))" "val i (\<pi> i)\<ge> 4/5"
    "\<forall>j\<in>  clusterNodes (Cluster B (pred (pred l))). val i (\<pi> i) \<ge> val j (\<pi> j)"
    using finite_sup_aux[OF finite_clusterNodes, of "Cluster B (pred (pred l))" "\<lambda>x. val x (\<pi> x)" ]
    by force
  have pi_i_not_def: "\<pi> i \<noteq>  clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l))) "
  proof (rule ccontr, goal_cases asm)
    case asm
    obtain j where j_def: "j \<in> clusterNodes (Cluster C l)" "val j (\<pi> j) < 4/5"
      using C1_ubound 
      by (smt (verit, best) BitM.simps(1) One_nat_def all_not_in_conv card_mono clusterCard_correct empty_subsetI example_2.clusterCard.simps(2) example_2.clusterCard.simps(3) finite_clusterNodes lessI linorder_not_le numeral_3_eq_3 numeral_eq_Suc numerals(1) pred_numeral_simps(2))
    have "\<pi> i \<inter> neighbors j = clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l))) - {j}"
      unfolding neighbors_correct_set[OF j_def(1)] using asm by auto
    moreover have "j \<in> \<pi> i" using j_def asm by auto
    hence "\<pi> i = \<pi> j" using partition_relation[OF assms j_def(1) i_def(1)] by auto
    ultimately have "\<pi> j \<inter> neighbors j = clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l))) - {j}  "
      "\<pi> j = clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l)))" using asm by auto
    hence "card (\<pi> j \<inter> neighbors j) = 4" "card (\<pi> j) = 5" using j_def(1) by auto
    hence "val j (\<pi> j) = 4 /5" using val_graph_correct[OF finite_pi'[OF assms j_def(1)], of j]
      unfolding val_graph_def by auto
    then show ?case using j_def(2) by auto
  qed
  have min_pi_i:"card (\<pi> i \<inter> neighbors i) \<ge> 4" using card_val_lower_bound[OF finite_pi'[OF assms i_def(1)] _ in_its_partition[OF assms i_def(1)]]
      unfolding f'_def(1) using i_def(2) by auto
  have "\<pi> i \<inter> clusterNodes (Cluster A (pred l)) \<noteq> {} \<or> \<pi> i \<inter> clusterNodes (Cluster A (pred (pred l))) \<noteq> {}"
  proof (rule ccontr, goal_cases asm)
    case asm
    hence  subset:"\<pi> i \<inter> neighbors i \<subseteq>  clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l))) - {i} "
      unfolding neighbors_correct_set[OF i_def(1)] by auto
    moreover have c_4:"card (...) = 4" using i_def(1) by auto
    ultimately have card_pi_neighbors:"card (\<pi> i \<inter> neighbors i) =4" using min_pi_i card_mono 
      by (smt (verit, best) finite.emptyI finite.insertI finite_Diff2 finite_Un finite_clusterNodes nle_le)
    hence pi_neighbors: "\<pi> i \<inter> neighbors i =  clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l))) - {i} "
      using c_4 subset  by (simp add: card_subset_eq finite_clusterNodes)
    have "card (\<pi> i) \<le> 5" using card_pi_neighbors i_def(2) 
      unfolding val_graph_correct[OF finite_pi'[OF assms i_def(1)], symmetric] val_graph_def
      by (smt (verit, best) frac_less2 nat_1_add_1 nat_le_real_less numeral_Bit1 numeral_code(2) of_nat_1 of_nat_add)
    hence "card (\<pi> i - neighbors i) \<le> 1" using card_pi_neighbors card_Un_disjoint[of "\<pi> i \<inter> neighbors i" "\<pi> i - neighbors i"]
        finite_subset[OF _ finite_pi'[OF assms i_def(1)]] 
      by (simp add: Int_Diff_Un Int_Diff_disjoint)
    moreover have "{i} \<subseteq> \<pi> i - neighbors i " using in_its_partition[OF assms i_def(1)] no_self_neighbor by auto
    ultimately have " \<pi> i - neighbors i = {i}" 
      by (metis (no_types, lifting) One_nat_def assms card.empty card_insert_if card_seteq equals0D finite.emptyI finite_Diff2 finite_neighbors finite_pi' i_def(1))
    hence "\<pi> i = clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l))) " using pi_neighbors i_def(1) by fast
   then show ?case using  pi_i_not_def by auto
 qed
  then obtain x c y where x_c_y_def: "x\<in> clusterNodes c"  "c  = Cluster A (pred l) \<or> c = Cluster A (pred (pred l))"
    "x \<in> \<pi> i" "y \<in> vertices" "clusterNodes c \<subseteq> \<pi> y" using A_superplayer[OF assms] 
    by (metis disjoint_iff)
  moreover then have "clusterNodes c \<subseteq> \<pi> i" using partition_relation[OF assms]
    by (metis UN_iff i_def(1) subsetD)
  ultimately have A4_or_A5:"clusterNodes (Cluster A (pred l)) \<subseteq> \<pi> i \<or> clusterNodes (Cluster A (pred (pred l))) \<subseteq> \<pi> i"
    using A_superplayer[OF assms] by blast
  have "\<not> clusterNodes (Cluster A (pred l)) \<union> clusterNodes (Cluster A (pred (pred l))) \<subseteq> \<pi> i "
  proof (rule ccontr, goal_cases A4_A5)
    case A4_A5
  let ?A4_C4= " clusterNodes (Cluster A (pred (pred l))) \<union> clusterNodes (Cluster C (pred (pred l)))"
    have "\<forall>j\<in> clusterNodes (Cluster A (pred (pred l))). val j (\<pi> j) < 5/6"
    proof(standard,goal_cases A4)
      case (A4 j)
      have "val j (\<pi> i) \<le> real 9 / (real 9 + real 3)"
      proof(rule card_val_upper_bound''[of "neighbors j" _ "clusterNodes (Cluster A (pred l))"], goal_cases)
        case 1
        then show ?case using A4 card_neighbors_A' by auto
      next
        case 2
        then show ?case by auto
      next
        case 3
        then show ?case by auto
      next
        case 4
        then show ?case by auto
      next
        case 5
        have "clusterNodes (Cluster A (pred l)) \<subseteq> \<pi> i" using A4_A5 by auto
        moreover have "clusterNodes (Cluster A (pred l)) \<inter> neighbors j = {}"
          unfolding neighbors_correct_set[OF A4] using pred_diff[of "pred l"]
          by (auto)+
        ultimately
        show ?case 
         by auto  
      next
        case 6
        then show ?case using finite_pi'[OF assms i_def(1)] by blast
      next
        case 7
        then show ?case using finite_neighbors by blast
      qed
      moreover have "j \<in> \<pi> i" using A4 A4_A5 by auto
      hence "\<pi> j = \<pi> i" using partition_relation[OF assms A4 i_def(1)] by auto
      ultimately show ?case by auto
    qed

    moreover have "\<forall>k\<in> clusterNodes (Cluster C (pred (pred l))). val k (\<pi> k) < 5/6"
    proof (standard, goal_cases C4)
      case (C4 k)
      have "\<pi> k = \<pi> i \<or> \<pi> k \<inter> \<pi> i = {}" 
        using partition_relation[OF assms C4 i_def(1)] by (auto split:if_splits)
      then show ?case
      proof(standard, goal_cases eq_ki disjoint_ki)
        case eq_ki
        moreover have "val k (\<pi> i) \<le> real 7 / (real 7 + real 3)"
        proof(rule card_val_upper_bound''[of "neighbors k" _ "clusterNodes (Cluster A (pred l))"], goal_cases)
          case 1
          then show ?case using C4 card_neighbors_C' by auto
        next
          case 2
          then show ?case by auto
        next
          case 3
          then show ?case by auto
        next
          case 4
          then show ?case by auto
        next
          case 5
          have "clusterNodes (Cluster A (pred l)) \<subseteq> \<pi> i" using A4_A5 by auto
          moreover have "clusterNodes (Cluster A (pred l)) \<inter> neighbors k = {}"
           unfolding neighbors_correct_set[OF C4] using pred_diff[of "pred l"]
           by (auto)+
         ultimately show ?case  by auto
        next
          case 6
          then show ?case using finite_pi'[OF assms i_def(1)] by auto
        next
          case 7
          then show ?case using finite_neighbors by auto
        qed
        ultimately show ?case by auto
      next
        case disjoint_ki
        have "val k (\<pi> k) \<le> real 4 / (real 4 + real 1)"
        proof (rule card_val_upper_bound''[of "neighbors k - clusterNodes (Cluster A (pred (pred l)))" _ "{k}"], goal_cases)
          case 1
          have "clusterNodes (Cluster A (pred (pred l))) \<subseteq> neighbors k"
            unfolding neighbors_correct_set[OF C4] using C4 clusterNodes_inter_empty by auto
          moreover have "card (clusterNodes (Cluster A (pred (pred l)))) = 3 " by auto
            ultimately show ?case using card_neighbors_C'[OF C4] by auto
        next
          case 2
          then show ?case by auto
        next
          case 3
          then show ?case by auto
        next
          case 4
          then show ?case using disjoint_ki A4_A5 by auto
        next
          case 5
          then show ?case using in_its_partition[OF assms C4] no_self_neighbor by blast
        next
          case 6
          then show ?case using finite_pi'[OF assms C4] by auto
        next
          case 7
          then show ?case using finite_neighbors by auto
        qed
        then show ?case by auto
      qed
    qed
    ultimately
    have "\<forall>j\<in>?A4_C4. val j (\<pi> j) < 5 / 6  "
      by auto
    moreover have "\<forall>j\<in>?A4_C4. val j (?A4_C4) = 5/6"
    proof(standard, goal_cases A4_C4)
      case (A4_C4 j)
      hence "?A4_C4 \<inter> neighbors j = ?A4_C4 - {j}"
      proof(standard, goal_cases A4 C4)
        case A4
        then show ?case unfolding neighbors_correct_set[OF A4] by  auto
      next
        case C4
        then show ?case unfolding neighbors_correct_set[OF C4] by  auto
      qed
      hence "card (?A4_C4 \<inter> neighbors j) = 5" using A4_C4 by auto
      moreover have "card (?A4_C4) = 6" by auto
      ultimately show ?case using A4_C4 
        unfolding val_graph_def
        by (metis (no_types, lifting) finite_Un finite_clusterNodes graph_FHG.val_graph_def graph_FHG_axioms of_nat_numeral val_graph_correct)
    qed
    ultimately have "blocking_coalition \<pi> ?A4_C4" unfolding blocking_coalition_def
      strict_pref_rel_def 
      by (smt (verit, ccfv_SIG) Sup_upper Un_subset_iff all_not_in_conv assms cluster_core_min_val example_2.Cluster.inject example_2.ClusterType.distinct(3) example_2.clusterEdge.simps(3) nle_le rangeI)
    then show ?case using assms unfolding core_def in_core_def by auto
  qed
  then obtain c c' where c_def:"{c,c'} = {Cluster A (pred l), Cluster A (pred (pred l))}"
"clusterNodes c \<subseteq> \<pi> i" " \<not> clusterNodes c' \<subseteq>\<pi> i " "c = Cluster A (pred l) \<or> c = Cluster A (pred (pred l))"
    using A4_or_A5 
    by blast
  then obtain y where y_def: "y \<in> clusterNodes c'" "y \<notin> \<pi> i"
     by blast
   moreover have c'_def: "c' =  Cluster A (pred l)\<or> c' = Cluster A (pred (pred l))"
     using  c_def(1) by auto
   then obtain x where x_def:  "x\<in> vertices" "clusterNodes c' \<subseteq> \<pi> x" 
     using A_superplayer[OF assms] by blast
   hence "y \<in> \<pi> x" using y_def by auto
   hence "\<pi> x \<noteq> \<pi> i" using y_def (2) by auto
   hence "\<pi> x \<inter> \<pi> i = {}" using partition_relation[OF assms] x_def(1) i_def(1)
     by (meson UN_iff)
   hence c'_notin:"\<pi> i \<inter> clusterNodes c' = {}" using x_def(2) by auto
   have in_its_neighbors:"\<pi> i - {i}  \<subseteq> neighbors i"
   proof (rule ccontr,goal_cases asm)
     case asm
     then obtain i' where i'_def: "i'\<in> \<pi> i" "i' \<notin> neighbors i" "i' \<noteq> i"
       by blast
     have "val i (\<pi> i) \<le> real 7 / (real 7 + real 2)"
     proof (rule card_val_upper_bound''[of "neighbors i - clusterNodes c'" _ "{i,i'}"] , goal_cases)
       case 1
       have "clusterNodes c' \<subseteq> neighbors i" unfolding neighbors_correct_set[OF i_def(1)]
         using i_def(1) clusterNodes_inter_empty c'_def by auto
       then show ?case using c'_def card_neighbors_B'[OF i_def(1)] by auto
     next
       case 2
       then show ?case using i'_def(3) by auto
     next
       case 3
       then show ?case by auto
     next
       case 4
       then show ?case using c'_notin by auto
     next
       case 5
       then show ?case using i'_def in_its_partition[OF assms i_def(1)] no_self_neighbor by auto
     next
       case 6
       then show ?case using finite_pi'[OF assms i_def(1)] by auto
     next
       case 7
       then show ?case using finite_neighbors by auto
     qed 
     then show ?case using i_def(2) by auto
   qed
   have "clusterNodes (Cluster B (pred (pred l))) \<subseteq> \<pi> i"
   proof (rule ccontr, goal_cases asm)
     case asm
     have "blocking_coalition \<pi> (\<pi> i \<union> clusterNodes (Cluster B (pred (pred l))))"
       using blocking_coalition_if_connected[OF i_def(1) i_def(3) _ _ asm in_its_neighbors assms]  
       by auto
     then show ?case using assms unfolding core_def in_core_def by auto
   qed
   obtain cl where cl_def:"c = Cluster A cl" "cl = pred l \<or> cl= pred (pred l)"
     using c_def(1) by auto
       let ?A4_C4="clusterNodes c \<union> clusterNodes (Cluster C cl)"
   have "\<forall>j\<in>clusterNodes c. val j (\<pi> j) < 5/6"
   proof (standard, goal_cases A4)
     case (A4 j)
     hence "j \<in> \<pi> i" using c_def(2) by auto
     hence "\<pi> j = \<pi> i" using partition_relation[OF assms A4 i_def(1)] by auto
     moreover have "val j (\<pi> i) \<le> real 4 / (real 4 + real 1)"
     proof (rule card_val_upper_bound''
         [of "clusterNodes c \<union> clusterNodes (Cluster B (pred (pred l))) - {j}" _ "{j}"], goal_cases)
       case 1
       then show ?case using c_def(4) A4 by auto
     next
       case 2
       then show ?case by auto
     next
       case 3
       then show ?case by auto
     next
       case 4
       have "clusterEdge (Cluster B (pred (pred l))) c"
         using c_def(4) by auto
       moreover have " Cluster B (pred (pred l)) \<noteq> c"
         using c_def(4) by auto
       ultimately have "neighbors i \<inter> neighbors j = clusterNodes c \<union> clusterNodes (Cluster B (pred (pred l))) - {i,j}"
         using neighbors_intersection[OF i_def(1) A4] no_triangle_cluster_plus 
          example_2.edge_means_neighboring(1) neighboring_clusters_correct by auto
       then show ?case using in_its_neighbors i_def(1) by auto
     next
       case 5
       then show ?case using A4 c_def(2) no_self_neighbor by auto
     next
       case 6
       then show ?case using finite_pi'[OF assms i_def(1)] .
     next
       case 7
       then show ?case using finite_clusterNodes by auto
     qed
     ultimately show ?case by auto
   qed
   moreover have "\<forall>k\<in> clusterNodes (Cluster C cl). val k (\<pi> k) < 5/6"
   proof(standard, goal_cases C4)
     case (C4 k)
     hence "k \<notin> neighbors i" "k \<noteq> i"
       unfolding neighbors_correct_set[OF i_def(1)] using i_def(1) C4 cl_def(2) by auto
     hence "k \<notin> \<pi> i" using in_its_neighbors by auto
     hence "\<pi> i \<inter> \<pi> k = {}" using partition_relation[OF assms C4 i_def(1)] by auto
     hence  * :"\<pi> k \<inter> clusterNodes c = {}" using c_def(2) by auto
     have "val k (\<pi> k) \<le> real 4 / (real 4 + real 1)"
     proof (rule card_val_upper_bound''[of "neighbors k - clusterNodes c" _ "{k}"], goal_cases)
       case 1
       have "clusterNodes c \<subseteq> neighbors k" unfolding neighbors_correct_set[OF C4]  cl_def(1) 
         using C4 by auto
       moreover have "card (clusterNodes c) = 3" using cl_def(1) by auto
       moreover have "card (neighbors k) = 7" using card_neighbors_C'[OF C4] . 
       ultimately show ?case using finite_clusterNodes finite_neighbors 
         by (simp add: card_Diff_subset)
     next
       case 2
       then show ?case by auto
     next
       case 3
       then show ?case by auto
     next
       case 4
       then show ?case using * by auto
     next
       case 5
       then show ?case using in_its_partition[OF assms C4] no_self_neighbor by auto
     next
       case 6
       then show ?case using finite_pi'[OF assms C4] by auto
     next
       case 7
       then show ?case using finite_neighbors by auto
     qed
     then show ?case by auto
   qed
   ultimately have "\<forall>j\<in> ?A4_C4. val j (\<pi> j) < 5/6" by auto
   moreover have "\<forall>j\<in>?A4_C4. val j (?A4_C4) = 5/6"
    proof(standard, goal_cases A4_C4)
      case (A4_C4 j)
      hence "?A4_C4 \<inter> neighbors j = ?A4_C4 - {j}"
      proof(standard, goal_cases A4 C4)
        case A4
        then show ?case unfolding neighbors_correct_set[OF A4] cl_def(1) by  auto
      next
        case C4
        then show ?case unfolding neighbors_correct_set[OF C4] cl_def(1) by  auto
      qed
      hence "card (?A4_C4 \<inter> neighbors j) = 5" using A4_C4 cl_def(1) by auto
      moreover have "card (?A4_C4) = 6" using cl_def(1) by auto
      ultimately show ?case using A4_C4 
        unfolding val_graph_def
        by (metis (no_types, lifting) finite_Un finite_clusterNodes graph_FHG.val_graph_def graph_FHG_axioms of_nat_numeral val_graph_correct)
    qed
    ultimately have "blocking_coalition \<pi> ?A4_C4" unfolding blocking_coalition_def
      strict_pref_rel_def 
      by (smt (verit, ccfv_SIG) IntE IntI UNIV_I UN_upper Un_iff x_c_y_def c'_def c'_notin c_def(2) c_def(3) c_def(4) empty_iff sup_least)
    then show ?case using assms unfolding core_def in_core_def by auto
  qed

lemma C_superplayer:
  fixes l \<pi>
  assumes "\<pi> \<in> core"
  shows "\<exists>x\<in> vertices. clusterNodes (Cluster C l) \<subseteq> \<pi> x"
proof (rule ccontr, goal_cases no_super_C)
  case no_super_C
  obtain i where i_def:" i\<in>clusterNodes (Cluster C l)" " 4 / 5 \<le> val i (\<pi> i)"
    using C_superplayer_aux[OF assms] by auto
  then obtain i where i_def: " i\<in>clusterNodes (Cluster C l)" " 4 / 5 \<le> val i (\<pi> i)"
 "\<forall>j\<in>clusterNodes (Cluster C l). val j (\<pi> j) \<le> val i (\<pi> i)"
    using finite_sup[OF finite_clusterNodes, of _ "\<lambda>i. val i (\<pi> i)"] 
    by (smt (verit) empty_iff)
  have * : "\<pi> i - {i} \<subseteq> neighbors i"
  proof (rule ccontr,goal_cases asm)
    case asm
    then obtain j where j_def: "j \<in> \<pi> i" "j \<noteq> i" "j \<notin> neighbors i" by auto
    have "val i (\<pi> i) \<le> real 7 / (real 7 + real 2)"
    proof (rule card_val_upper_bound''[of "neighbors i" _ "{i,j}"], goal_cases)
      case 1
      then show ?case using card_neighbors_C' i_def(1) by auto
    next
      case 2
      then show ?case using j_def(2) by auto
    next
      case 3
      then show ?case by auto
    next
      case 4
      then show ?case by auto
    next
      case 5
      then show ?case using j_def in_its_partition[OF assms i_def(1)] no_self_neighbor by blast
    next
      case 6
      then show ?case using finite_pi'[OF assms i_def(1)] by auto
    next
      case 7
      then show ?case using finite_neighbors by auto
    qed
    then show ?case using i_def(2) by auto
  qed
  have ** : "\<not> clusterNodes (Cluster C l) \<subseteq> \<pi> i" using no_super_C  i_def(1) by blast
  have "blocking_coalition \<pi> ( clusterNodes (Cluster C l) \<union> \<pi> i )"
    by (rule blocking_coalition_if_connected[OF i_def(1) i_def(3) _ _ ** * assms]) auto
  then show ?case using assms unfolding core_def in_core_def by auto
qed

lemma A_superplayer':
  fixes \<pi> l i c
  assumes "\<pi> \<in> core"
    and "i \<in> clusterNodes c"
  shows "clusterNodes (Cluster A l) \<subseteq> \<pi> i \<or> clusterNodes (Cluster A l) \<inter> \<pi> i = {}"
proof -
  obtain x cx where x_def:"x \<in> clusterNodes cx" "clusterNodes (Cluster A l) \<subseteq> \<pi> x"
    using A_superplayer[OF assms(1)] 
    by (meson UN_iff)
  moreover then  have "\<pi> x = \<pi> i \<or> \<pi> x \<inter> \<pi> i = {}" using partition_relation[OF assms(1) x_def(1) assms(2)]
    by (auto split:if_splits)
  ultimately show ?thesis by auto
qed

lemma C_superplayer':
  fixes \<pi> l i c
  assumes "\<pi> \<in> core"
    and "i \<in> clusterNodes c"
  shows "clusterNodes (Cluster C l) \<subseteq> \<pi> i \<or> clusterNodes (Cluster C l) \<inter> \<pi> i = {}"
proof -
  obtain x cx where x_def:"x \<in> clusterNodes cx" "clusterNodes (Cluster C l) \<subseteq> \<pi> x"
    using C_superplayer[OF assms(1)] 
    by (meson UN_iff)
  moreover then  have "\<pi> x = \<pi> i \<or> \<pi> x \<inter> \<pi> i = {}" using partition_relation[OF assms(1) x_def(1) assms(2)]
    by (auto split:if_splits)
  ultimately show ?thesis by auto
qed

lemma 
  fixes \<pi>
  assumes "\<pi> \<in> core"
  shows False
proof (cases "\<exists>i l. i\<in> clusterNodes (Cluster A l) \<and> \<not> \<pi> i - {i} \<subseteq> neighbors i")
  case True
  then obtain i l i' where i_def: "i\<in> clusterNodes (Cluster A l)" "i' \<in> \<pi> i" "i' \<noteq> i" "i' \<notin> neighbors i" " \<not> \<pi> i - {i} \<subseteq> neighbors i"
    by blast
  show ?thesis
  proof(cases "\<exists>Y. \<pi> i = clusterNodes (Cluster A l) \<union>  clusterNodes (Cluster C l) \<union> Y \<and> Y \<noteq> {} \<and> Y \<subseteq> clusterNodes (Cluster B (pred (pred l)))")
    case True
    then obtain Y where pi_def: " \<pi> i = clusterNodes (Cluster A l) \<union>  clusterNodes (Cluster C l) \<union> Y"
      "Y \<noteq> {}" " Y \<subseteq> clusterNodes (Cluster B (pred (pred l)))" by auto
    have A1_ubound: "\<forall>j\<in> clusterNodes (Cluster A l). val j (\<pi> j) < 4/5"
    proof (standard, goal_cases A1)
      case (A1 j)
      hence j_pi:"j \<in> \<pi> i" using pi_def(1) by auto
      hence "\<pi> j = \<pi> i" using partition_relation[OF assms A1 i_def(1)] by auto
      moreover have "val j (\<pi> i) \<le> real 5 / ( real 5 + real 2)"
      proof (rule card_val_upper_bound''[of "clusterNodes (Cluster A l) \<union>  clusterNodes (Cluster C l) - {j}" _ "{i',j}"], goal_cases)
        case 1
        then show ?case using A1 by auto
      next
        case 2
        then show ?case using i_def(1) 
          by (metis (no_types, lifting) A1 One_nat_def Suc_1 card.empty card_insert_if example_2.clusterEdge.simps(1) finite.emptyI finite.insertI i_def(3) i_def(4) insert_absorb insert_not_empty neighbor_check singleton_insert_inj_eq)
      next
        case 3
        then show ?case by auto
      next
        case 4
        have "neighbors j \<inter> clusterNodes (Cluster B (pred (pred l))) = {}" using pred_diff unfolding neighbors_correct_set[OF A1]
          using clusterNodes_inter_empty  by auto
        hence "neighbors j \<inter> Y = {}" using pi_def(3) by auto
        then show ?case unfolding pi_def using no_self_neighbor by auto
      next
        case 5
        have "i' \<notin> neighbors j" 
          by (metis (mono_tags, lifting) A1 Un_iff i_def(1) i_def(3) i_def(4) same_cluster_neighbors singletonD)
        then show ?case using j_pi i_def(2) no_self_neighbor[of j] by auto
      next
        case 6
        then show ?case using finite_pi'[OF assms i_def(1)] by auto
      next
        case 7
        then show ?case using finite_clusterNodes by auto
      qed
      ultimately show ?case by auto
    qed
    obtain j where "j\<in> clusterNodes (Cluster A l) \<union> clusterNodes (Cluster B l)" 
        "val j (\<pi> j) \<ge> 4/5" using cluster_core_min_val[of "Cluster A l" "Cluster B l"]
      unfolding f'_def 
      using assms by auto
    hence j_def:"j\<in> clusterNodes (Cluster B l)" 
        "val j (\<pi> j) \<ge> 4/5" using A1_ubound by auto
    then obtain j where j_def: "j\<in> clusterNodes (Cluster B l)" 
        "val j (\<pi> j) \<ge> 4/5" "\<forall>j'\<in> clusterNodes (Cluster B l). val j (\<pi> j) \<ge> val j' (\<pi> j') "
      using finite_sup[OF finite_clusterNodes, of "Cluster B l" "\<lambda>x. val x (\<pi> x)"]
      by force
     have "j \<notin> \<pi> i" using pi_def(1,3) j_def(1) clusterNodes_inter_empty 
          by (metis UnE example_2.Cluster.inject example_2.ClusterType.distinct(1) example_2.ClusterType.distinct(5) not_in_many_clusters' pred2_diff subsetD)
        hence "\<pi> j \<inter> \<pi> i = {}" using partition_relation[OF assms j_def(1) i_def(1)] by auto
        hence not_A1: "\<pi> j \<inter> clusterNodes (Cluster A l) = {}" using pi_def by auto
    have j_in_neighbors:"\<pi> j - {j} \<subseteq> neighbors j"
    proof (rule ccontr, goal_cases asm)
      case asm
      then obtain j' where j'_def: "j' \<in> \<pi> j" "j' \<noteq> j" "j' \<notin> neighbors j" by blast
      have "val j (\<pi> j) \<le> real 7 / (real 7 + real 2)"
      proof (rule card_val_upper_bound''[of "neighbors j - clusterNodes (Cluster A l)" _ "{j,j'}"], goal_cases)
        case 1
        have "clusterNodes (Cluster A l) \<subseteq> neighbors j "
          unfolding neighbors_correct_set[OF j_def(1)] using j_def(1) clusterNodes_inter_empty by auto 
        then show ?case using card_neighbors_B'[OF j_def(1)] by auto 
      next
        case 2
        then show ?case using j'_def(2) by auto
      next
        case 3
        then show ?case by auto
      next
        case 4
        then show ?case using not_A1 by auto
      next
        case 5
        then show ?case using j'_def in_its_partition[OF assms j_def(1)] no_self_neighbor by blast
      next
        case 6
        then show ?case using finite_pi'[OF assms j_def(1)] .
      next
        case 7
        then show ?case using finite_neighbors by blast
      qed
      then show ?case using j_def(2) by auto
    qed
    have B1_pi:"clusterNodes (Cluster B l) \<subseteq> \<pi> j"
    proof (rule ccontr, goal_cases asm)
      case asm
      hence "blocking_coalition \<pi> (\<pi> j \<union> clusterNodes (Cluster B l) )"
        using blocking_coalition_if_connected[OF j_def(1) j_def(3)_ _ asm  j_in_neighbors assms]
        by auto
      then show ?case using assms unfolding core_def in_core_def by auto
    qed
    have pi_clusterNodes:"\<pi> j \<subseteq>  \<Union> (clusterNodes ` (neighboring_clusters (Cluster B l)))"
      using pi_in_neighbors  unfolding neighbors_correct_set[OF j_def(1)]
      by (metis Diff_eq_empty_iff Diff_insert2 UN_I neighbors_correct_set[OF j_def(1)] in_neighboring insert_Diff j_def(1) j_in_neighbors)
    from A_superplayer'[OF assms j_def(1), of "Suc l" ] 
        C_superplayer'[OF assms j_def(1), of "Suc (Suc l)" ] 
    show ?thesis 
    proof (auto simp del:clusterNodes.simps, goal_cases)
      case 1
      have pi_j:"\<pi> j = clusterNodes (Cluster B l) \<union> clusterNodes (Cluster A (Suc l)) \<union> 
                  clusterNodes (Cluster C (Suc (Suc l)))"
      proof (standard, goal_cases left right)
        case left
        then show ?case using pi_clusterNodes
           not_A1  unfolding neighbors_correct_set[OF j_def(1)] 
          by (auto simp del:clusterNodes.simps)
      next
        case right
        then show ?case using 1 B1_pi by auto
      qed
      have "\<forall>k\<in> clusterNodes (Cluster C (Suc (Suc l))). val k (\<pi> k) = 4/8"
      proof(standard, goal_cases C3)
        case (C3 k)
        hence "k \<in> \<pi> j" using pi_j by auto
        hence "\<pi> k = \<pi> j" using partition_relation[OF assms C3 j_def(1)] by auto
        moreover have "(\<pi> j \<inter> neighbors k) = clusterNodes (Cluster B l) \<union>
                  clusterNodes (Cluster C (Suc (Suc l))) - {k} "
          unfolding neighbors_correct_set[OF C3] pi_j     
          apply (auto simp del:clusterNodes.simps)
          using clusterNodes_inter_empty  suc_diff 
          by (meson example_2.Cluster.inject not_in_many_clusters')
        moreover have "card (...) = 4" using C3 by auto
        moreover have "card (\<pi> j) = 8" unfolding pi_j by auto
        ultimately show ?case unfolding val_graph_correct[OF finite_pi'[OF assms C3],symmetric]
          val_graph_def by auto
      qed
      moreover have "\<forall>k \<in> clusterNodes (Cluster C (Suc (Suc l))). val k (clusterNodes (Cluster C (Suc (Suc l)))) = 2/3"
      proof(standard, goal_cases C3)
        case (C3 k)
        have "clusterNodes (Cluster C (Suc (Suc l))) \<inter> neighbors k = clusterNodes (Cluster C (Suc (Suc l))) - {k}"
          unfolding neighbors_correct_set[OF C3] by auto
        moreover have "card (...) = 2" using C3 by auto
        moreover have "card (clusterNodes (Cluster C (Suc (Suc l)))) = 3" by auto
        ultimately show ?case  unfolding val_graph_correct[OF finite_clusterNodes ,symmetric]
          val_graph_def by auto
      qed
      ultimately have "blocking_coalition \<pi> (clusterNodes (Cluster C (Suc (Suc l))))"
        unfolding blocking_coalition_def strict_pref_rel_def  
        apply (auto simp del:clusterNodes.simps)
        by auto
      then show ?case using assms unfolding core_def in_core_def by auto
    next
      case 2
      have pi_j:"\<pi> j = clusterNodes (Cluster B l) \<union> clusterNodes (Cluster A (Suc l))"
      proof (standard, goal_cases left right)
        case left
        then show ?case using pi_clusterNodes
           not_A1 2(2)  unfolding neighbors_correct_set[OF j_def(1)] 
          by (auto simp del:clusterNodes.simps)
      next
        case right
        then show ?case using 2(1) B1_pi by auto
      qed
      let ?A2_C2= "clusterNodes (Cluster A (Suc l)) \<union> clusterNodes (Cluster C (Suc l))"
      have "\<forall>k\<in> clusterNodes (Cluster A (Suc l)). val k (\<pi> k) = 4/5"
      proof (standard, goal_cases A2)
        case (A2 k)
        have "k \<in> \<pi> j" using A2 pi_j by auto
        hence "\<pi> k = \<pi> j" using partition_relation[OF assms A2 j_def(1)] by auto
        moreover have "\<pi> j \<inter> neighbors k = \<pi> j - {k} "
          unfolding pi_j neighbors_correct_set[OF A2] by auto
        moreover have "card(...) = 4"  unfolding pi_j using A2  by auto
        moreover have "card (\<pi> j) = 5" unfolding pi_j   by auto
        ultimately show ?case unfolding val_graph_correct[OF finite_pi'[OF assms A2],symmetric] val_graph_def 
          by auto
      qed
      moreover have "\<forall>k \<in>  clusterNodes (Cluster C (Suc l)). val k (\<pi> k) \<le> 4/5 "
      proof (standard, goal_cases C2)
        case (C2 k)
        have "k \<notin> \<pi> j" unfolding pi_j using C2 by auto
        hence "\<pi> k \<inter> \<pi> j = {}" using partition_relation[OF assms C2 j_def(1)] by auto
        hence  * :"\<pi> k \<inter> clusterNodes (Cluster A (Suc l)) = {}" unfolding pi_j by auto
        have "val k (\<pi> k) \<le> real 4 / (real 4 + real 1)" 
        proof (rule card_val_upper_bound''[of "neighbors k - clusterNodes (Cluster A (Suc l)) " _ "{k}"], 
              goal_cases)
          case 1
          then show ?case unfolding neighbors_correct_set[OF C2] using C2 by auto
        next
          case 2
          then show ?case by auto
        next
          case 3
          then show ?case by auto
        next
          case 4
          then show ?case using * by auto
        next
          case 5
          then show ?case using in_its_partition[OF assms C2] no_self_neighbor by blast
        next
          case 6
          then show ?case using finite_pi'[OF assms C2] .
        next
          case 7
          then show ?case using finite_neighbors by auto
        qed
        then show ?case by auto
      qed
      ultimately have "\<forall>k \<in> ?A2_C2. val k (\<pi> k ) \<le> 4/5" by auto
      moreover have "\<forall>k \<in> ?A2_C2. val k ?A2_C2 = 5/6"
      proof(standard, goal_cases A2_C2)
        case (A2_C2 k)
        hence "?A2_C2 \<inter> neighbors k = ?A2_C2 - {k}"
        proof(standard,goal_cases A2 C2)
          case A2
          then show ?case unfolding neighbors_correct_set[OF A2] by auto
        next
          case C2
          then show ?case unfolding neighbors_correct_set[OF C2] by auto
        qed
        moreover have "card(...) = 5" using A2_C2 by auto
        moreover have "card ?A2_C2 = 6" by auto
        ultimately show ?case using val_graph_correct[symmetric] finite_clusterNodes unfolding val_graph_def by auto
      qed
      ultimately have "\<forall>k \<in> ?A2_C2. strict_pref_rel ?A2_C2 k (\<pi> k)"
        unfolding strict_pref_rel_def by auto
      hence "blocking_coalition \<pi> ?A2_C2 " unfolding blocking_coalition_def
        apply (auto simp del:clusterNodes.simps)
        apply auto
        done
      then show ?case using assms unfolding core_def in_core_def by auto
    next
      case 3
      have pi_j:"\<pi> j = clusterNodes (Cluster B l) \<union> clusterNodes (Cluster C (Suc (Suc l)))"
      proof (standard, goal_cases left right)
        case left
        then show ?case using pi_clusterNodes
           not_A1 3(1)  unfolding neighbors_correct_set[OF j_def(1)] 
          by (auto simp del:clusterNodes.simps)
      next
        case right
        then show ?case using 3(2) B1_pi by auto
      qed
        
      then show ?case sorry
    next
      case 4
      then show ?case sorry 
    qed
  next
    case False
    let ?A1_C1= "clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l)"
    have "\<forall> j\<in> clusterNodes (Cluster A l). val j (\<pi> j) < 5/6"
    proof (standard, goal_cases A1)
      case (A1 j)
      hence * :"j \<in> \<pi> i" using A_superplayer'[OF assms i_def(1)] in_its_partition[OF assms i_def(1)] i_def(1)
        by blast
      hence "\<pi> j = \<pi> i" using partition_relation[OF assms A1 i_def(1)] by auto
      moreover have "val j (\<pi> i) \<le> real 9 / (real 9 + real 2)"
      proof(rule card_val_upper_bound''[of "neighbors j" _ "{j,i'}"], goal_cases)
        case 1
        then show ?case using A1 card_neighbors_A' by auto
      next
        case 2
        have "j \<noteq> i'" 
          using A1 example_2.clusterEdge.simps(1) i_def(1) i_def(3) i_def(4) neighbor_check by blast
        then show ?case by auto
      next
        case 3
        then show ?case by auto
      next
        case 4
        then show ?case by auto
      next
        case 5
        have "i' \<notin> neighbors j" using i_def(3) i_def(4) unfolding neighbors_correct_set[OF A1]
            neighbors_correct_set[OF i_def(1)] by auto
        then show ?case using i_def(2) * no_self_neighbor by blast
      next
        case 6
        then show ?case using finite_pi'[OF assms i_def(1)] .
      next
        case 7
        then show ?case using finite_neighbors by auto
      qed
      ultimately show ?case  by auto
    qed
    moreover have "\<forall> j\<in> clusterNodes (Cluster C l). val j (\<pi> j) < 5/6" 
      using C_superplayer'[OF assms i_def(1), of l]
    proof(standard, goal_cases C1_in C1_out)
      case C1_in
        show ?case
      proof(standard, goal_cases C1)
        case (C1 j)
        have "\<exists>i'\<in> \<pi> i. i' \<noteq> j \<and> i' \<notin> neighbors j "
        proof (rule ccontr,goal_cases asm)
          case asm
          hence "\<pi> i - {j} \<subseteq>  neighbors j" by auto
          hence "\<pi> i \<subseteq> neighbors j \<union> {j}" by auto
          hence "\<pi> i \<subseteq> clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l) \<union>  clusterNodes (Cluster B (pred (pred l)))"
             unfolding neighbors_correct_set[OF C1] using C1 by (auto simp del:clusterNodes.simps)
          moreover have "\<not> \<pi> i \<subseteq> neighbors i \<union> {i}"
            using in_its_partition[OF assms i_def(1)] i_def(5) by auto
          hence "\<not> \<pi> i \<subseteq> clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l)"
            using i_def(1) unfolding neighbors_correct_set[OF i_def(1)]
            by (auto simp del:clusterNodes.simps)
          ultimately obtain Y where  "\<pi> i = clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l) \<union> Y"
            "Y \<noteq> {}" "Y \<subseteq> clusterNodes (Cluster B (pred (pred l)))"
            by (smt (verit, ccfv_threshold) C1_in Diff_eq_empty_iff Diff_iff Diff_subset_conv Int_Un_distrib Int_Un_eq(3) Int_insert_right_if1 Un_Diff_cancel assms example_2.A_superplayer' example_2.in_its_partition i_def(1) inf.absorb_iff1 inf_commute insertCI insert_Diff sup_commute)
          then show ?case using False by blast
        qed
        then obtain i' where i'_def: "i' \<in> \<pi> i" "i' \<noteq> j" "i' \<notin> neighbors j " by blast         
        have  * :"j \<in> \<pi> i" using C1 C1_in by auto
        hence "\<pi> j = \<pi> i" using partition_relation[OF assms C1 i_def(1)] by auto
        moreover have "val j (\<pi> i) \<le> real 7 / (real 7 + real 2)"
      proof(rule card_val_upper_bound''[of "neighbors j" _ "{j,i'}"], goal_cases)
        case 1
        then show ?case using C1 card_neighbors_C' by auto
      next
        case 2
        have "j \<noteq> i'" using i'_def(2) by simp
        then show ?case by auto
      next
        case 3
        then show ?case by auto
      next
        case 4
        then show ?case by auto
      next
        case 5
        then show ?case using * no_self_neighbor i'_def by auto
      next
        case 6
        then show ?case using finite_pi'[OF assms i_def(1)] .
      next
        case 7
        then show ?case using finite_neighbors by auto
      qed
      ultimately show ?case  by auto
    qed 
    next
      case C1_out
       show ?case
      proof(standard, goal_cases C1)
        case (C1 j)
        have "val j (\<pi> j ) \<le> real 4 / (real 4 + real 1)"
        proof (rule card_val_upper_bound''[of "neighbors j - clusterNodes (Cluster A l)" _ "{j}"], goal_cases)
          case 1
          then show ?case unfolding neighbors_correct_set[OF C1] using C1 by auto
        next
          case 2
          then show ?case by auto
        next
          case 3
          then show ?case by auto
        next
          case 4
          have "clusterNodes (Cluster A l) \<subseteq> \<pi> i" using A_superplayer'[OF assms i_def(1), of l] in_its_partition[OF assms i_def(1)]
            i_def(1) by auto
          moreover have "j \<notin> \<pi> i" using C1_out C1 by auto
          hence "\<pi> j \<inter> \<pi> i = {}" using partition_relation[OF assms C1 i_def(1)] by auto
          ultimately have "\<pi> j \<inter> clusterNodes (Cluster A l) = {}" by auto
          then show ?case by auto
        next
          case 5
          then show ?case using in_its_partition[OF assms C1] no_self_neighbor by blast 
        next
          case 6
          then show ?case using finite_pi'[OF assms C1] .
        next
          case 7
          then show ?case using finite_neighbors by auto
        qed
        then show ?case by auto
      qed
    qed
    moreover have "\<forall>j\<in>?A1_C1. val j (?A1_C1) = 5/6"
    proof(standard, goal_cases A1_C1)
      case (A1_C1 j)
      hence "?A1_C1 \<inter> neighbors j = ?A1_C1 - {j}"
      proof(standard,goal_cases A1 C1)
        case A1
        then show ?case unfolding neighbors_correct_set[OF A1] using  A1 by auto
      next
        case C1
        then show ?case unfolding neighbors_correct_set[OF C1] using  C1 by auto
      qed
      moreover have "card(...) = 5" using A1_C1 by auto
      moreover have "card(?A1_C1) = 6" by auto        
      ultimately show ?case using val_graph_correct finite_clusterNodes unfolding val_graph_def
        by (metis (no_types, lifting) finite_UnI of_nat_numeral)
    qed
    ultimately have "\<forall>j\<in>?A1_C1. strict_pref_rel ?A1_C1 j (\<pi> j)"
      unfolding strict_pref_rel_def by auto
    hence "blocking_coalition \<pi> ?A1_C1" unfolding blocking_coalition_def 
      apply (auto simp del:clusterNodes.simps)
      apply auto
      done
    then show ?thesis using assms unfolding core_def in_core_def by auto
  qed
next
  case False
  have * :"\<forall>l. \<exists>j \<in> clusterNodes (Cluster C l).  \<pi> j - {j} \<subseteq> neighbors j"
  proof (rule ccontr, goal_cases asm)
    case asm
    then obtain l where "\<forall>j\<in>clusterNodes (Cluster C l). \<not> \<pi> j - {j} \<subseteq> neighbors j" by blast
    then obtain j j' where j_def: "j \<in> clusterNodes (Cluster C l)" "val j (\<pi> j) \<ge> 4/5"
        "j' \<in> \<pi> j" "j \<noteq> j'" "j' \<notin> neighbors j"
      using C_superplayer_aux[OF assms] by blast
    have "val j (\<pi> j) \<le> real 7 / (real 7 + real 2)"
    proof (rule card_val_upper_bound''[of "neighbors j" _ "{j,j'}"], goal_cases)
      case 1
      then show ?case using card_neighbors_C'[OF j_def(1)] .
    next
      case 2
      then show ?case using j_def(4) by auto
    next
      case 3
      then show ?case by auto
    next
      case 4
      then show ?case by auto
    next
      case 5
      then show ?case using in_its_partition[OF assms j_def(1)] no_self_neighbor j_def(3,5)
        by blast
    next
      case 6
      then show ?case using finite_pi'[OF assms j_def(1)] .
    next
      case 7
      then show ?case using finite_neighbors by auto
    qed
    then show ?case using j_def(2) by auto
  qed
  have "\<forall>l. \<exists>j \<in> clusterNodes (Cluster C l).  \<pi> j - {j} \<subseteq> neighbors j \<and> val j (\<pi> j ) \<ge> 4/5"
  proof (standard, goal_cases)
    case (1 l)
    obtain j where j_def: "j \<in> clusterNodes (Cluster C l)" "val j (\<pi> j ) \<ge> 4/5" using C_superplayer_aux[OF assms] by blast
    obtain j' where j'_def:"j' \<in> clusterNodes (Cluster C l)" "\<pi> j' \<subseteq> neighbors j' \<union> {j'}" using * by blast
    hence "clusterNodes (Cluster C l) \<subseteq> \<pi> j'" using C_superplayer'[OF assms j'_def(1)] in_its_partition[OF assms j'_def(1)]
      by auto
    hence "j \<in> \<pi> j'" using j_def(1) by auto
    hence "\<pi> j' = \<pi> j" using partition_relation[OF assms j_def(1) j'_def(1)] by auto
    moreover have "neighbors j' \<union> {j'} = neighbors j \<union> {j}" unfolding neighbors_correct_set[OF j_def(1)] neighbors_correct_set[OF j'_def(1)]
      using j_def(1) j'_def(1) by auto
    ultimately have "\<pi> j \<subseteq> neighbors j \<union> {j}" using j'_def(2) by auto
    hence "\<pi> j - {j} \<subseteq> neighbors j" using no_self_neighbor by blast
    then show ?case using j_def by blast
  qed
  hence"\<exists>j. \<forall>l. j l \<in> clusterNodes (Cluster C l) \<and>  \<pi> (j l) - {(j l)} \<subseteq> neighbors (j l) \<and> val (j l) (\<pi> (j l) ) \<ge> 4/5"
    by meson
  then obtain j where j_def: "\<forall>l. j l \<in> clusterNodes (Cluster C l) \<and>  \<pi> (j l) - {(j l)} \<subseteq> neighbors (j l) \<and> val (j l) (\<pi> (j l) ) \<ge> 4/5"
    by blast
  have no_pattern: "\<not> (\<exists>l Y. \<pi> (j l) = clusterNodes(Cluster A l) \<union> clusterNodes (Cluster C l) \<union> Y \<and> Y \<noteq> {} \<and> Y \<subseteq> clusterNodes (Cluster B (pred (pred l))))"
  proof (rule ccontr, goal_cases asm)
    case asm
    then obtain l Y where pi_def: "\<pi> (j l) = clusterNodes(Cluster A l) \<union> clusterNodes (Cluster C l) \<union> Y " " Y \<noteq> {}" "Y \<subseteq> clusterNodes (Cluster B (pred (pred l)))"
      by blast
    then obtain b i where i_def: "i \<in> clusterNodes (Cluster A l)"  "b \<in> Y" "b \<in> clusterNodes (Cluster B (pred (pred l)))"
      by auto
    hence "\<pi> i - {i} \<subseteq> neighbors i" using False by blast
    moreover have "i \<in> \<pi> (j l)" using pi_def(1) i_def(1) by auto
    hence "\<pi> (j l) = \<pi> i" using partition_relation[OF assms i_def(1), of "j l"] j_def 
      by metis
    hence "b \<in> \<pi> i" using i_def(2) pi_def(1) by blast
    moreover have "b \<noteq> i" using i_def(1,3) by auto
    moreover have "b \<notin> neighbors i" unfolding neighbors_correct_set[OF i_def(1)] 
      using clusterNodes_inter_empty i_def(3)
      by (metis (no_types, lifting) neighbors_correct_set[OF i_def(1)] example_2.clusterEdge.simps(2) i_def(1) neighbor_check pred2_diff suc_pred)
    ultimately show ?case by auto
  qed
  have * : "\<forall>l. \<pi> (j l) = clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l) \<or> \<pi> (j l) = clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l)))"
  proof (rule ccontr, goal_cases asm)
    case asm
    then obtain l where not_pi_def: "\<pi> (j l) \<noteq> clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l)"
"\<pi> (j l) \<noteq> clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l)))" by blast
    have * :"clusterNodes (Cluster C l) \<subseteq> \<pi> (j l)" using j_def C_superplayer'[OF assms, of  "j l" "Cluster C l"]
        in_its_partition[OF assms, of  "j l" "Cluster C l"] by blast
    have ** :"\<pi>(j l) \<subseteq>  clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l)))"
      using j_def neighbors_correct_set[of "j l" "Cluster C l"] by (auto simp del:clusterNodes.simps)
    have  *** :"j l \<in> clusterNodes (Cluster C l)" using j_def by auto
    show ?case using A_superplayer'[OF assms ***, of l]
    proof (standard, goal_cases A B)
      case A
      then show ?case using not_pi_def(1) no_pattern * apply (auto simp del:clusterNodes.simps)
        by (smt (verit, best) "**" Diff_subset_conv Int_Diff_Un Int_Un_distrib inf.absorb_iff2 not_pi_def(1) sup_bot.right_neutral)
    next
      case B
      hence "\<pi> (j l) \<subseteq> clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l)))" using ** by auto
      hence "\<pi> (j l) \<inter> neighbors (j l) \<subseteq> clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l))) - {j l} "
        using no_self_neighbor by auto
      moreover have "card (...) = 4" using *** by auto
      moreover have "card(\<pi> (j l) \<inter> neighbors (j l)) \<ge> 4" using card_val_lower_bound[OF finite_pi'[OF assms ***] _ in_its_partition[OF assms ***]]
        unfolding f'_def using j_def by auto
      ultimately have  pi_neighbors: "\<pi> (j l) \<inter> neighbors (j l)  = clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l))) - {j l}"  "card(\<pi> (j l) \<inter> neighbors (j l)) = 4"
        by (smt (verit, best) card.infinite card_mono card_subset_eq le_antisym zero_neq_numeral) +
      hence "card (\<pi> (j l)) \<le> 5" using j_def using val_graph_correct[OF finite_pi'[OF assms ***], of "j l" , symmetric] unfolding val_graph_def
        by (metis (no_types, lifting) "*" \<open>\<pi> (j l) \<subseteq> clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l)))\<close> inf_le1 insert_Diff insert_subset not_pi_def(2) subset_antisym)
      hence "card (\<pi> (j l) - neighbors (j l)) \<le> 1" using pi_neighbors(2) card_Un_disjoint[of "\<pi> (j l) \<inter> neighbors (j l)" "\<pi> (j l) - neighbors (j l)"
, OF finite_subset[OF _ finite_pi'[OF assms ***]] finite_subset[OF _ finite_pi'[OF assms ***]]]
        by (metis (no_types, lifting) Diff_subset Int_Diff_Un Int_Diff_disjoint Nat.add_diff_assoc One_nat_def add_Suc_right diff_add_inverse2 diff_is_0_eq eq_imp_le eval_nat_numeral(3) inf_le1 nat_add_left_cancel_le)
      moreover have "{j l} \<subseteq> \<pi> (j l) - neighbors (j l)" using no_self_neighbor in_its_partition[OF assms ***] by auto
      ultimately have "\<pi> (j l) - neighbors (j l) = { j l} " 
        by (smt (verit, del_insts) Diff_iff insert_Diff insert_subset j_def subsetI subset_antisym)
      hence "\<pi> (j l) = clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l)))" using pi_neighbors(1) ***
        by (smt (verit) Int_Diff_Un UnI1 Un_insert_right insert_Diff_single insert_absorb sup_bot.right_neutral)
      then show ?case using not_pi_def(2) by simp  
    qed
  qed
  have "\<forall>l i. i \<in> clusterNodes (Cluster A l) \<longrightarrow> \<pi> i = clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l)
        \<or> \<pi> i \<subseteq> clusterNodes (Cluster A l) \<union> clusterNodes (Cluster B l)  \<union> clusterNodes (Cluster B (pred l))"
  proof(standard, standard, standard, goal_cases A_l )
    case (A_l l i)
    have  *** :"j l \<in> clusterNodes (Cluster C l)" using j_def by auto
    from * 
    have "\<pi> (j l) = clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l) \<or> \<pi> (j l) = clusterNodes (Cluster C l) \<union> clusterNodes (Cluster B (pred (pred l)))"
      by simp
    then show ?case
    proof (standard, goal_cases)
      case 1
      hence "i \<in> \<pi> (j l)" using A_l by auto
      hence "\<pi> (j l) = \<pi> i" using partition_relation[OF assms A_l ***] by auto
      then show ?case using 1 by auto
    next
      case 2
      hence "i \<notin> \<pi> (j l)" using A_l by auto
      hence "\<pi> (j l) \<inter> \<pi> i = {}" using partition_relation[OF assms A_l ***] by auto
      hence "\<pi> i \<inter> clusterNodes (Cluster C l) = {}" using 2 by auto
      moreover have "\<pi> i \<subseteq> neighbors i \<union> {i}"
        using A_l False by auto
      hence "\<pi> i \<subseteq> \<Union> (clusterNodes ` neighboring_clusters (Cluster A l))"
            unfolding neighbors_correct_set[OF A_l] using A_l by (auto simp del:clusterNodes.simps)
      ultimately show ?thesis by (auto simp del:clusterNodes.simps)
    qed
  qed
  then consider (1) "\<forall>l i. i \<in> clusterNodes (Cluster A l) \<longrightarrow> \<pi> i = clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l)"
              | (2) "\<exists>l i. i \<in> clusterNodes (Cluster A l) \<and> \<pi> i \<subseteq> clusterNodes (Cluster A l) \<union> clusterNodes (Cluster B l)  \<union> clusterNodes (Cluster B (pred l)) "
    by blast
  then show False
  proof(cases)
    case 1
      obtain l where "l=O1" by blast
    have "\<forall>l. \<forall>j\<in> clusterNodes (Cluster B l). val j (\<pi> j) \<le> 1/2"
    proof (standard +, goal_cases Bl)
      case (Bl l j)
      have int_empty:"\<forall>l'. (clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l')) \<inter> \<pi> j = {}"
      proof
        fix l'
        obtain i where i_def: "i \<in> clusterNodes (Cluster A l')"  by auto
        hence pi: "\<pi> i = clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l')" using 1 
          by presburger
        hence "j \<notin> \<pi> i" using Bl by auto
        hence "\<pi> i \<inter> \<pi> j = {}" using partition_relation[OF assms Bl i_def(1)] by auto
        thus " (clusterNodes (Cluster A l') \<union> clusterNodes (Cluster C l')) \<inter> \<pi> j = {} " using pi by auto
      qed
      have "val j (\<pi> j ) \<le> real 1 / (real 1 + real 1)"
      proof (rule card_val_upper_bound''[of " clusterNodes (Cluster B l) - {j}" _ "{j}"], goal_cases)
        case 1
        then show ?case using Bl by auto
      next
        case 2
        then show ?case by auto
      next
        case 3
        then show ?case by auto
      next
        case 4
        then show ?case unfolding neighbors_correct_set[OF Bl]
          using int_empty Bl by (auto simp del:clusterNodes.simps)
      next
        case 5
        then show ?case using in_its_partition[OF assms Bl] no_self_neighbor by auto
      next
        case 6
        then show ?case using finite_pi'[OF assms Bl] .
      next
        case 7
        then show ?case using finite_clusterNodes by auto
      qed
      then show ?case by auto
    qed
    hence "\<forall>j \<in> clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l)). val j (\<pi> j) \<le> 1/2"
      by blast
    moreover 
    let ?coalition= "clusterNodes (Cluster A l) \<union> clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l))"
    have "\<forall>i \<in> clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l)). val i ?coalition = 4/7"
    proof (standard, goal_cases B)
      case (B i)
      then obtain b where b_def: "i \<in> clusterNodes b" "b = Cluster B l \<or> b = Cluster B (pred l)"
        by blast
      hence "?coalition \<inter> neighbors i = (clusterNodes b \<union> clusterNodes (Cluster A l)) - {i}"
        unfolding neighbors_correct_set[OF b_def(1)]
        apply (auto simp del: clusterNodes.simps)
        using not_in_many_clusters' by auto
      moreover have  "card (...) = 4" using b_def by auto
      moreover have "card ?coalition = 7" by auto
      ultimately show ?case using val_graph_correct[symmetric] finite_clusterNodes unfolding
            val_graph_def by auto
    qed
    ultimately have  * :"\<forall>i \<in> clusterNodes (Cluster B l) \<union> clusterNodes (Cluster B (pred l)).
        strict_pref_rel ?coalition i (\<pi> i) "
      unfolding strict_pref_rel_def by auto
    have "\<forall>i\<in> clusterNodes (Cluster A l). val i ?coalition = 6/7"
     proof(standard, goal_cases A1)
      case (A1 i)
          have "?coalition \<inter> neighbors i = ?coalition - {i}" unfolding neighbors_correct_set[OF A1]
        by auto
      then show ?case using val_graph_correct[symmetric] finite_clusterNodes
            val_graph_def using A1 by auto
    qed 
    moreover have "\<forall>i \<in> clusterNodes (Cluster A l). val i (\<pi> i) = 5/6"
    proof(standard, goal_cases A1)
      case (A1 i)
      hence "\<pi> i = clusterNodes (Cluster A l) \<union> clusterNodes (Cluster C l)"
        using 1 by blast
      moreover then have "\<pi> i \<inter> neighbors i = \<pi> i - {i}" unfolding neighbors_correct_set[OF A1]
        by auto
      ultimately show ?case unfolding val_graph_correct[OF finite_pi'[OF assms A1], symmetric]
            val_graph_def using A1 by auto
    qed
    ultimately have "\<forall>i \<in>  clusterNodes (Cluster A l). strict_pref_rel ?coalition i (\<pi> i) "
      unfolding strict_pref_rel_def by auto
    hence "\<forall>i \<in> ?coalition. strict_pref_rel ?coalition i (\<pi> i)" using * by blast
    moreover have "?coalition \<noteq> {}" by auto
    ultimately have "blocking_coalition \<pi> ?coalition"
      unfolding blocking_coalition_def by blast
    then show ?thesis using assms unfolding core_def in_core_def by blast
  next
    case 2
    then show ?thesis sorry
  qed

  
  

  then show ?thesis sorry
qed



end                                            
                                                     