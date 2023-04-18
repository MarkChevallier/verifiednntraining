theory STL
  imports Complex_Main

begin

fun timeline :: "real \<Rightarrow> 'v::real_vector" where
"timeline r = 0"

datatype 'v::real_vector constraint = cMu "'v \<Rightarrow> real" real | cNot "'v constraint" 
  | cAnd "'v constraint" "'v constraint" | cUntil real real "'v constraint" "'v constraint"

fun eval :: "(real \<Rightarrow> 'v::real_vector) \<Rightarrow> real \<Rightarrow> 'v constraint \<Rightarrow> bool" where
"eval t l (cMu f r) = (if l<0 then False else ((f (t 0)) > r))"
| "eval t l (cNot c) = (if l<0 then False else (\<not>(eval t l c)))"
| "eval t l (cAnd c1 c2) = (if l<0 then False else 
  ((eval t l c1) \<and> (eval t l c2)))"
| "eval t l (cUntil x y c1 c2) = 
  (if l<0 then False else (\<exists>t'\<ge>x. t'\<le>y \<and> eval (\<lambda>r. t (r+t')) (l-t') c2 
    \<and> (\<forall>t''. t''\<ge>x\<and>t''\<le>t' \<longrightarrow> eval (\<lambda>r. t (r+t'')) (l-t'') c1)))"

end