From RFXP Require Import Features Xp DT DTXp.

Module Type JustClassifierInstance (F : FeatureSig) (O : Output) (C : ClassifierOn F O).
    Parameter k : C.t.
End JustClassifierInstance.

Module Type DTInstance := FeatureSig <+ Output <+ DTOn <+ JustClassifierInstance.


Fixpoint initConstraintFull {n : nat} (fs : featureSig n) : featureSpaceConstraint fs :=
    match fs with
    | featureSigNil => featureSpaceConstraintNil
    | featureSigCons _ fs =>
        featureSpaceConstraintCons constraintInitFull (initConstraintFull fs)
    end.

Module DtGenVectors (Dt : DTInstance).

    Fixpoint gen_aux
            (C : featureSpaceConstraint Dt.fs)
            (dt : Dt.t)
            (acc : list (featureVec Dt.fs))
            : list (featureVec Dt.fs) :=
        match dt with
        | Leaf c =>
            match witness C with
            | Some v => v :: acc
            | None => acc
            end
        | Node i test dt1 dt2 =>
            let Cleft := splitLeft i test C in
            let CRight := splitRight i test C in
            let acc := gen_aux Cleft dt1 acc in
            gen_aux CRight dt2 acc
        end.
    
    Definition gen : unit -> list (featureVec Dt.fs) := fun _ =>
        gen_aux (initConstraintFull Dt.fs) Dt.k nil.

End DtGenVectors.