theory Print
  imports Show.Show_Instances "HOL-Library.Code_Char"
begin

subsection \<open>Printing\<close>

text \<open>Taken from AFP-entry "Affine-Arithmetic".\<close>

definition print_raw :: "String.literal \<Rightarrow> unit" where "print_raw x = ()"

abbreviation "print \<equiv> (\<lambda>a b. let _ = print_raw (String.implode (show a)) in b)"

definition echo :: "'a \<Rightarrow> 'a::show" where "echo x = print x x"

code_printing constant print_raw \<rightharpoonup> (SML) "writeln"

lemma echo_id: "echo = (\<lambda>x. x)"
  by (rule, simp add: echo_def)

subsection \<open>File Output\<close>

definition file_output :: "String.literal \<Rightarrow> ((String.literal \<Rightarrow> unit) \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "file_output _ f = f (\<lambda>_. ())"

code_printing constant file_output \<rightharpoonup> (SML) "(fn s => fn f => File.open'_output (fn os => f (File.output os)) (Path.explode s))"

subsection \<open>Timing\<close>

typedecl ('a, 'b) cpu_timer
typedecl time

consts start_cpu_timer :: "unit \<Rightarrow> ('a, 'b) cpu_timer"
consts check_cpu_timer :: "('a, 'b) cpu_timer \<Rightarrow> (time \<times> time)"
consts time_to_string :: "time \<Rightarrow> String.literal"

definition check_cpu_timer_string :: "('a, 'b) cpu_timer \<Rightarrow> String.literal"
  where "check_cpu_timer_string t =
    (let (usr, sys) = check_cpu_timer t in (STR (''User: '') + time_to_string usr) + STR (''  System: '') + time_to_string sys)"

definition timing_raw :: "String.literal \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "timing_raw s f = (let tmr = (start_cpu_timer ())::(nat, nat) cpu_timer;
                         res = f ();
                         _ = print_raw (s + check_cpu_timer_string tmr) in res)"

definition timing_raw_nores :: "String.literal \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> unit"
  where "timing_raw_nores s f = (let tmr = (start_cpu_timer ())::(nat, nat) cpu_timer;
                         res = f ();
                         _ = print_raw (s + check_cpu_timer_string tmr) in ())"

abbreviation "timing \<equiv> (\<lambda>v. timing_raw (STR '''') (\<lambda>_. v))"
abbreviation "timing_nores \<equiv> (\<lambda>v. timing_raw_nores (STR '''') (\<lambda>_. v))"
abbreviation "timing_lbl \<equiv> (\<lambda>s v. timing_raw (String.implode s + STR '': '') (\<lambda>_. v))"

lemma timing_raw_id: "timing_raw s f = f ()"
  by (simp add: timing_raw_def)

code_printing
type_constructor cpu_timer \<rightharpoonup>
    (SML) "_ Timer.cpu_timer"
| type_constructor time \<rightharpoonup>
    (SML) "Time.time"
| constant start_cpu_timer \<rightharpoonup>
    (SML) "Timer.startCPUTimer"
| constant check_cpu_timer \<rightharpoonup>
    (SML) "(fn ct => (let val {usr, sys} = Timer.checkCPUTimer ct in (usr, sys) end))"
| constant time_to_string \<rightharpoonup>
    (SML) "Time.toString"

end (* theory *)
