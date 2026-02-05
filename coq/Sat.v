From RFXP Require Import CNF.

Module Type SatSolver.

    Variant ans := SAT (I : assignment nat) | UNSAT.

    Parameter solve : cnf nat -> ans.

End SatSolver.

Module Type IsCorrectSatSolver (Import Sat : SatSolver).

    Axiom sat_correct : forall (c : cnf nat) (I : assignment nat),
        solve c = SAT I -> eval_cnf I c = true.

    Axiom unsat_correct : forall (c : cnf nat) (I : assignment nat),
        solve c = UNSAT -> eval_cnf I c = false.

End IsCorrectSatSolver.

Module Type CorrectSatSolver := SatSolver <+ IsCorrectSatSolver.


Module Type CCEncoder.

    Parameter encode : cnf_with_cc nat -> cnf nat.

End CCEncoder.

Module Type IsCorrectCCEncoder (Import Enc : CCEncoder).

    Axiom encode_correct : forall (c : cnf_with_cc nat) (I : assignment nat),
        eval_cnf I (encode c) = eval_cnf_with_cc I c.

End IsCorrectCCEncoder.

Module Type CorrectCCEncoder := CCEncoder <+ IsCorrectCCEncoder.