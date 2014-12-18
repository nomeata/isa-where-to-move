theory Where_To_Move_Ex2
imports Main
begin

definition "bar = False"

lemma barE: "bar \<Longrightarrow>P" unfolding bar_def by (erule FalseE)

end
