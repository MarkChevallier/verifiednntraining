theory Int_Gen
  imports Complex_Main
begin

code_printing
  type_constructor int \<rightharpoonup>
    (SML) "int"
    and (OCaml) "int"

code_printing
  type_constructor integer \<rightharpoonup>
    (OCaml) "int"

code_printing
  constant "(-) :: int \<Rightarrow> int \<Rightarrow> int" \<rightharpoonup>
    (SML) "Int.- ((_), (_))"
    and (OCaml) "Stdlib.(-)"

code_printing
  constant "(+) :: int \<Rightarrow> int \<Rightarrow> int" \<rightharpoonup>
    (SML) "Int.+ ((_), (_))"
    and (OCaml) "Stdlib.(+)"

code_printing
  constant "(div) :: integer \<Rightarrow> integer \<Rightarrow> integer" \<rightharpoonup>
    (OCaml) "_ '/  _"

code_printing
  constant "(mod) :: int \<Rightarrow> int \<Rightarrow> int" \<rightharpoonup>
    (OCaml) "_ mod _"

code_printing
  constant "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool" \<rightharpoonup>
    (SML) "Int.(<=) ((_), (_))"
    and (OCaml) "Stdlib.(<=)"

code_printing
  constant "0 :: int" \<rightharpoonup>
    (SML) "0"
    and (OCaml) "0"

code_printing
  constant "1 :: int" \<rightharpoonup>
    (SML) "1"
    and (OCaml) "1"

end