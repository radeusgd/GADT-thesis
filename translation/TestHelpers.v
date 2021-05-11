Require Import Helpers.
Require Import Library.
Require Import Coq.Arith.Compare_dec.

Print le_gt_dec.

Definition lift_rec_avar (k: nat) (w: nat) (a: avar) : avar :=
  match a with
  | avar_b i => if le_gt_dec k i then avar_b (w + i) else avar_b i
  | avar_f x => avar_f x
end.

Definition lift_rec_path (k: nat) (w: nat) (p: path): path :=
  match p with
  | p_sel x bs => p_sel (lift_rec_avar k w x) bs
  end.

Fixpoint lift_rec_typ (k: nat) (w: nat) (T: typ): typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (lift_rec_dec k w D)
  | T1 ∧ T2        => lift_rec_typ k w T1 ∧ lift_rec_typ k w T2
  | p ↓ L          => lift_rec_path k w p ↓ L
  | μ T            => μ (lift_rec_typ (S k) w T)
  | ∀(T1) T2      => ∀(lift_rec_typ k w T1) lift_rec_typ (S k) w T2
  | {{ p }}        => {{ lift_rec_path k w p }}
  end
with lift_rec_dec (k: nat) (u: nat) (D: dec): dec :=
  match D with
  | { A >: T <: U } => { A >: lift_rec_typ k u T <: lift_rec_typ k u U }
  | { a ⦂ T } => { a ⦂ lift_rec_typ k u T }
  end.

Fixpoint lift_rec_trm (k: nat) (u: nat) (t: trm): trm :=
  match t with
  | trm_val v      => trm_val (lift_rec_val k u v)
  | trm_path p     => trm_path (lift_rec_path k u p)
  | trm_app p q    => trm_app (lift_rec_path k u p) (lift_rec_path k u q)
  | trm_let t1 t2  => trm_let (lift_rec_trm k u t1) (lift_rec_trm (S k) u t2)
  end
with lift_rec_val (k: nat) (u: nat) (v: val): val :=
  match v with
  | ν(T)ds   => ν (lift_rec_typ (S k) u T) lift_rec_defs (S k) u ds
  | λ(T) e  => λ(lift_rec_typ k u T) lift_rec_trm (S k) u e
  end
with lift_rec_def (k: nat) (u: nat) (d: def): def :=
  match d with
  | def_typ A T => def_typ A (lift_rec_typ k u T)
  | { a := t } => { a := lift_rec_defrhs k u t }
  end
with lift_rec_defs (k: nat) (u: nat) (ds: defs): defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons tl d => defs_cons (lift_rec_defs k u tl) (lift_rec_def k u d)
  end
with lift_rec_defrhs (k: nat) (u: nat) (drhs: def_rhs) : def_rhs :=
  match drhs with
  | defp p => defp (lift_rec_path k u p)
  | defv v => defv (lift_rec_val k u v)
  end.

Definition shift1_typ (t : typ) : typ := lift_rec_typ 0 1 t.
Definition shift1_trm (t : trm) : trm := lift_rec_trm 0 1 t.
Definition shift1_p (p : path) : path := lift_rec_path 0 1 p.
