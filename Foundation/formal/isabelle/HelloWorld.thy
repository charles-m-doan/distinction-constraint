theory HelloWorld
  imports Main
begin

lemma and_left: "A \<and> B \<longrightarrow> A"
proof
  assume h: "A \<and> B"
  from h show A by simp
qed

end