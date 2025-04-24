Require Import String.
From RFXP Require Import Utils.

Import StringSet.

Definition enum (s : StringSet.t) := { x : string | In x s }.