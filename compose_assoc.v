(*
Proof that function composition is associative,
even without assuming functional extensionality.
 *)

Require Import Basics.

Open Scope program_scope.

Theorem compose_assoc : forall (A : Set) (f g h : A -> A),
    f ∘ (g ∘ h) = (f ∘ g) ∘ h.
Proof.
  reflexivity.
Qed.
