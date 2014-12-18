theory Where_To_Move_Ex1
imports Main
begin

definition "foo = True"
print_theorems

lemma fooI: foo unfolding foo_def..

end
