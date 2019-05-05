(** Proof that for every two-parameter uncurried function, there
    exists an equivalent curried function *)

Definition curry (f : Type * Type -> Type) x y := f (x, y).

Theorem curry_exists :
  forall (f : (Type * Type) -> Type) x y, exists g, f (x, y) = g x y.
Proof.
  intros.
  exists (curry f).
  unfold curry.
  reflexivity.
Qed.
