theory Tensor_Mul
  imports Tensor_Binary_Op
begin


instantiation tensor:: (semigroup_mult) times
begin
  definition times_def: "A * B = binop times A B"
  instance ..
end

lemma lookup_times:
  fixes A :: "('a::semigroup_mult) tensor"
  assumes "is \<lhd> (dims A)" and "dims A = dims B"
  shows "lookup (A * B) is = (lookup A is) * (lookup B is)"
  by (metis assms(1) assms(2) lookup_binop times_def)

lemma times_assoc:
  assumes dimsA:"dims A = ds" and dimsB:"dims B = ds" and dimsC:"dims C = ds"
  shows "(A * B) * C = A * (B * C)"
by (rule tensor_lookup_eqI; simp add: times_def dimsA dimsB dimsC mult.assoc)+

end