theory Print
  imports Show.Show_Instances "HOL-Library.Code_Char"
begin

text \<open>Taken from AFP-entry "Affine-Arithmetic".\<close>

definition print_raw :: "String.literal \<Rightarrow> unit" where "print_raw x = ()"

definition file_output :: "String.literal \<Rightarrow> ((String.literal \<Rightarrow> unit) \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "file_output _ f = f (\<lambda>_. ())"

code_printing constant file_output \<rightharpoonup> (SML) "(fn s => fn f => File.open'_output (fn os => f (File.output os)) (Path.explode s))"

abbreviation "print \<equiv> print_raw \<circ> String.implode \<circ> show"

definition echo :: "'a \<Rightarrow> 'a::show" where "echo x = (let _ = print x in x)"

code_printing constant print_raw \<rightharpoonup> (SML) "writeln"

lemma echo_id: "echo = (\<lambda>x. x)"
  by (rule, simp add: echo_def)

end (* theory *)
