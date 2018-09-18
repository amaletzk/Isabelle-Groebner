theory Signature_Timings
  imports "../Signature_Groebner/Signature_Examples" "../Finite_Field"
begin

value [code] "timing (gb_sig_z_pprod (POT DRLEX) rw_rat_strict_pprod ((katsura DRLEX 1)::(_ \<Rightarrow>\<^sub>0 rat) list))"

(*
Timings on benchmark problems
=============================
ATTENTION! "d-pot" in [Eder+Faugere 2017] is NOT the same as "DEG POT!"

All tests were performed with "POT DRLEX" and "rw_rat_strict_pprod".


Coefficients in gf32003, on qftquad3:

Problem       Time (s)      #Basis      #0-Reductions
-----------------------------------------------------
Cyclic-6          1.7         155           8
Cyclic-7        660.0         749          36
Katsura-7         2.2         117           0
Katsura-8        28.8         225           0
Katsura-9       505.1         450           0
Eco-8             0.9          76           0
Eco-9             3.0         143           0
Eco-10           29.0         282           0
Eco-11          234.0         559           0
Noon-5            0.3          83           0
Noon-6            6.7         206           0
Noon-7          135.6         524           0


Rational coefficients, on qftquad4:

Problem       Time (s)      #Basis      #0-Reductions
-----------------------------------------------------
Cyclic-4          0.0           7           1
Cyclic-5          0.1          39           0
Cyclic-6          2.0         155           8
Cyclic-7        544.7         749          36
Katsura-5         0.1          29           0
Katsura-6         0.9          59           0
Katsura-7        22.4         117           0
Katsura-8      1005.4         225           0
Eco-8             0.5          76           0
Eco-9             3.0         143           0
Eco-10           32.0         282           0
Eco-11          297.2         559           0
Noon-5            0.4          83           0
Noon-6            8.8         206           0
Noon-7          213.5         524           0
*)

end (* theory *)
