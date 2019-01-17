theory Print
  imports Show.Show HOL.Rat
begin

subsection \<open>Instances of the Show-class\<close>

text \<open>We do not import "Show.Show_Instances", because we provide a different, more efficient
  instantiation for @{typ rat}.
  The other instances (for @{typ unit}, @{typ nat}, etc.) are copied from "Show.Show_Instances".\<close>

definition showsp_unit :: "unit showsp"
where
  "showsp_unit p x = shows_string ''()''"

lemma show_law_unit [show_law_intros]:
  "show_law showsp_unit x"
  by (rule show_lawI) (simp add: showsp_unit_def show_law_simps)

abbreviation showsp_char :: "char showsp"
where
  "showsp_char \<equiv> shows_prec"

lemma show_law_char [show_law_intros]:
  "show_law showsp_char x"
  by (rule show_lawI) (simp add: show_law_simps)

primrec showsp_bool :: "bool showsp"
where
  "showsp_bool p True = shows_string ''True''" |
  "showsp_bool p False = shows_string ''False''"

lemma show_law_bool [show_law_intros]:
  "show_law showsp_bool x"
  by (rule show_lawI, cases x) (simp_all add: show_law_simps)

primrec pshowsp_prod :: "(shows \<times> shows) showsp"
where
  "pshowsp_prod p (x, y) = shows_string ''('' o x o shows_string '', '' o y o shows_string '')''"

definition showsp_prod :: "'a showsp \<Rightarrow> 'b showsp \<Rightarrow> ('a \<times> 'b) showsp"
where
  [code del]: "showsp_prod s1 s2 p = pshowsp_prod p o map_prod (s1 1) (s2 1)"

lemma showsp_prod_simps [simp, code]:
  "showsp_prod s1 s2 p (x, y) =
    shows_string ''('' o s1 1 x o shows_string '', '' o s2 1 y o shows_string '')''"
  by (simp add: showsp_prod_def)

lemma show_law_prod [show_law_intros]:
  "(\<And>x. x \<in> Basic_BNFs.fsts y \<Longrightarrow> show_law s1 x) \<Longrightarrow>
   (\<And>x. x \<in> Basic_BNFs.snds y \<Longrightarrow> show_law s2 x) \<Longrightarrow>
    show_law (showsp_prod s1 s2) y"
proof (induct y)
  case (Pair x y)
  note * = Pair [unfolded prod_set_simps]
  show ?case
    by (rule show_lawI)
       (auto simp del: o_apply intro!: o_append intro: show_lawD * simp: show_law_simps)
qed

fun string_of_digit :: "nat \<Rightarrow> string"
where
  "string_of_digit n =
    (if n = 0 then ''0''
    else if n = 1 then ''1''
    else if n = 2 then ''2''
    else if n = 3 then ''3''
    else if n = 4 then ''4''
    else if n = 5 then ''5''
    else if n = 6 then ''6''
    else if n = 7 then ''7''
    else if n = 8 then ''8''
    else ''9'')"

fun showsp_nat :: "nat showsp"
where
  "showsp_nat p n =
    (if n < 10 then shows_string (string_of_digit n)
    else showsp_nat p (n div 10) o shows_string (string_of_digit (n mod 10)))"
declare showsp_nat.simps [simp del]

lemma show_law_nat [show_law_intros]:
  "show_law showsp_nat n"
  by (rule show_lawI, induct n rule: nat_less_induct) (simp add: show_law_simps showsp_nat.simps)

lemma showsp_nat_append [show_law_simps]:
  "showsp_nat p n (x @ y) = showsp_nat p n x @ y"
  by (intro show_lawD show_law_intros)

definition showsp_int :: "int showsp"
where
  "showsp_int p i =
    (if i < 0 then shows_string ''-'' o showsp_nat p (nat (- i)) else showsp_nat p (nat i))"

lemma show_law_int [show_law_intros]:
  "show_law showsp_int i"
  by (rule show_lawI, cases "i < 0") (simp_all add: showsp_int_def show_law_simps)

lemma showsp_int_append [show_law_simps]:
  "showsp_int p i (x @ y) = showsp_int p i x @ y"
  by (intro show_lawD show_law_intros)

fun showsp_natural :: "natural showsp"
where
  "showsp_natural p n =
    (if n < 10 then shows_string (string_of_digit (nat_of_natural n))
    else showsp_natural p (n div 10) o shows_string (string_of_digit (nat_of_natural (n mod 10))))"
declare showsp_natural.simps [simp del]

lemma showsp_nat_showsp_natural: "showsp_nat p n = showsp_natural p (natural_of_nat n)"
proof (induct n rule: nat_less_induct)
  case (1 n)
  show ?case
    by (subst showsp_nat.simps, subst showsp_natural.simps)
       (smt 1 div_less_dividend divide_natural.rep_eq less_natural.rep_eq modulo_natural.rep_eq
        nat_of_natural_inverse nat_of_natural_numeral nat_of_natural_of_nat_inverse not_gr_zero
        one_less_numeral_iff semiring_norm(76) zero_less_numeral)
qed

corollary showsp_natural_showsp_nat: "showsp_natural p n = showsp_nat p (nat_of_natural n)"
  by (simp add: showsp_nat_showsp_natural)

lemma show_law_natural [show_law_intros]: "show_law showsp_natural n"
  by (rule show_lawI, simp add: showsp_natural_showsp_nat showsp_nat_append)

lemma showsp_natural_append [show_law_simps]:
  "showsp_natural p n (x @ y) = showsp_natural p n x @ y"
  by (intro show_lawD show_law_intros)

definition showsp_integer :: "integer showsp"
where
  "showsp_integer p i =
    (if i < 0 then shows_string ''-'' o showsp_natural p (natural_of_integer (- i)) else showsp_natural p (natural_of_integer i))"

lemma show_law_integer [show_law_intros]: "show_law showsp_integer i"
  by (rule show_lawI, cases "i < 0", simp_all add: showsp_integer_def show_law_simps)

lemma showsp_integer_append [show_law_simps]:
  "showsp_integer p i (x @ y) = showsp_integer p i x @ y"
  by (intro show_lawD show_law_intros)

definition showsp_rat :: "rat showsp"
where
  "showsp_rat p x =
    (case quotient_of x of (d, n) \<Rightarrow>
      if n = 1 then
        showsp_integer p (integer_of_int d) else
        showsp_integer p (integer_of_int d) o shows_string ''/'' o showsp_integer p (integer_of_int n))"

lemma show_law_rat [show_law_intros]:
  "show_law showsp_rat r"
  by (rule show_lawI, cases "quotient_of r") (simp add: showsp_rat_def show_law_simps)

lemma showsp_rat_append [show_law_simps]:
  "showsp_rat p r (x @ y) = showsp_rat p r x @ y"
  by (intro show_lawD show_law_intros)

local_setup {*
  Show_Generator.register_foreign_partial_and_full_showsp @{type_name prod} 0
       @{term "pshowsp_prod"}
       @{term "showsp_prod"} (SOME @{thm showsp_prod_def})
       @{term "map_prod"} (SOME @{thm prod.map_comp}) [true, true]
       @{thm show_law_prod}
  #> Show_Generator.register_foreign_showsp @{typ unit} @{term "showsp_unit"} @{thm show_law_unit}
  #> Show_Generator.register_foreign_showsp @{typ bool} @{term "showsp_bool"} @{thm show_law_bool}
  #> Show_Generator.register_foreign_showsp @{typ char} @{term "showsp_char"} @{thm show_law_char}
  #> Show_Generator.register_foreign_showsp @{typ nat} @{term "showsp_nat"} @{thm show_law_nat}
  #> Show_Generator.register_foreign_showsp @{typ int} @{term "showsp_int"} @{thm show_law_int}
  #> Show_Generator.register_foreign_showsp @{typ rat} @{term "showsp_rat"} @{thm show_law_rat}
  #> Show_Generator.register_foreign_showsp @{typ natural} @{term "showsp_natural"} @{thm show_law_natural}
  #> Show_Generator.register_foreign_showsp @{typ integer} @{term "showsp_integer"} @{thm show_law_integer}
*}

derive "show" option sum prod unit bool nat int rat natural integer

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
    (let (usr, sys) = check_cpu_timer t in (STR ''User: '' + time_to_string usr) + STR ''  System: '' + time_to_string sys)"

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
