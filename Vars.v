Require Import List1 Var.

Notation Vars := (list1 Var).

Definition In_Vars_dec := In1_dec eq_var_dec.

Definition vars_eq := eq (A := Vars).
