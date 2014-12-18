theory Where_To_Move_Ex4
imports Where_To_Move_Ex3 Where_To_Move 
begin

lemma fooI2: "foo" by (rule fooI)
lemma barE2: "bar \<Longrightarrow> P" by (rule barE)
lemma foobar: "foo \<and> \<not> bar"
  apply rule
  apply (rule fooI)
  apply (rule notI)
  apply (erule barE)
  done
lemma foobar2: "foo \<and> \<not> bar"
  apply rule
  apply (rule fooI2)
  apply (rule notI)
  apply (erule barE2)
  done

where_to_move

end
