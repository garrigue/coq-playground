From mathcomp Require Import all_ssreflect.
Require Import PeanoNat Wf_nat.

Set Implicit Arguments.
Unset Strict Implicit.

Inductive term (n : nat) : Type :=
  | Var : 'I_n -> term n
  | Abs : term n.+1 -> term n
  | App : term n -> term n -> term n.

Fixpoint shift n (m : 'I_n.+1) (t : term n) : term n.+1 :=
  match t with
  | Var k => Var (lift m k)
  | App t1 t2 => App (shift m t1) (shift m t2)
  | Abs t1 => Abs (shift (lift ord0 m) t1)
  end.

Definition weaken n m (t : term n) : n <= m -> term m.
elim: t m => {n} [n k | n t IH | n t1 IH1 t2 IH2] m leqnm.
- have/Ordinal: k < m by apply/leq_trans.
  exact/Var.
- apply/Abs/IH.
  by rewrite ltnS.
- exact/App/IH1/leqnm/IH2.
Defined.

Inductive uterm : Type :=
  | UVar : nat -> uterm
  | UAbs : uterm -> uterm
  | UApp : uterm -> uterm -> uterm.

Fixpoint erase n (t : term n) : uterm :=
  match t with
  | Var k => UVar k
  | App t1 t2 => UApp (erase t1) (erase t2)
  | Abs t1 => UAbs (erase t1)
  end.

Lemma shift_unchanged n (t : term n) :
  erase (shift (Ordinal (ltnSn n)) t) = erase t.
Proof.
elim: n / t => [n k | n t IH | n t1 IH1 t2 IH2] /=.
- by rewrite /bump leqNgt ltn_ord.
- rewrite -IH.
  do 3!f_equal.
  by apply val_inj.
- congruence.
Qed.

(* 依存型での代入 *)
Fixpoint substv n (m : 'I_n.+1) (u : term n) (t : term n.+1) : term n :=
  match t with
  | Var k => if unlift m k is Some k' then Var k' else u
  | Abs t1 => Abs (substv (lift ord0 m) (shift ord0 u) t1)
  | App t1 t2 => App (substv m u t1) (substv m u t2)
  end.

Reserved Notation "t =>1 t'" (at level 70, no associativity).
Reserved Notation "t =>p t'" (at level 70, no associativity).

Inductive beta1 : forall n, term n -> term n -> Prop :=
  | babs n (t t' : term n.+1) :
      t =>1 t' -> Abs t =>1 Abs t'
  | bapp1 n (t1 t2 t1' : term n) :
      t1 =>1 t1' -> App t1 t2 =>1 App t1' t2
  | bapp2 n (t1 t2 t2' : term n) :
      t2 =>1 t2' -> App t1 t2 =>1 App t1 t2'
  | bbeta n (t1 : term n.+1) (t2 : term n) :
      App (Abs t1) t2 =>1 substv ord0 t2 t1
  where "t =>1 t'" := (beta1 t t').

Inductive par : forall n, term n -> term n -> Prop :=
  | pvar n (m : 'I_n) : Var m =>p Var m
  | pabs n (t t' : term n.+1) : t =>p t' -> Abs t =>p Abs t'
  | papp n (t1 t2 t1' t2' : term n) :
      t1 =>p t1' -> t2 =>p t2' -> App t1 t2 =>p App t1' t2'
  | pbeta n (t1 t1' : term n.+1) (t2 t2' : term n) :
      t1 =>p t1' -> t2 =>p t2' -> App (Abs t1) t2 =>p substv ord0 t2' t1'
  where "t =>p t'" := (par t t').

Fixpoint fullpar n (t : term n) {struct t} :=
  match t with
  | Var k => Var k
  | Abs t1 => Abs (fullpar t1)
  | App (Abs t1) t2 => substv ord0 (fullpar t2) (fullpar t1)
  | App t1 t2 => App (fullpar t1) (fullpar t2)
  end.

Definition term_eq_dec n (x y : term n) : decidable (x = y).
Proof.
elim: x y => {n} [n k | n t IH | n t1 IH1 t2 IH2] [k' | t' | t1' t2'];
  try by right.
- case H: (k == k').
  + rewrite (eqP H); by left.
  + right => -[] Hk.
    by rewrite Hk eqxx in H.
- case: (IH t') => [->|] ; by [left | right => -[] Ht].
- case: (IH1 t1') => [->|] ; [| by right => -[] Ht].
  case: (IH2 t2') => [->|] ; by [left | right => -[] Ht].
Defined.

Fixpoint height n (t : term n) :=
  match t with
  | Var _ => 1
  | Abs t1 => (height t1).+1
  | App t1 t2 => (maxn (height t1) (height t2)).+1
  end.

Definition fit n (j : 'I_n) := widen_ord (leqnSn n) j.

Lemma shiftC n (j k : 'I_n.+1) (t : term n) :
  j <= k ->
  shift (fit j) (shift k t) = shift (lift ord0 k) (shift j t).
Proof.
elim: t j k => {n} [n i | n t1 IH | n t1 IH1 t2 IH2] j k Hj /=.
- f_equal; apply val_inj => /=.
  rewrite [RHS]bumpC.
  by rewrite /bump /unbump leq0n add1n ltnS ltnNge Hj (subn1 k.+1).
- congr Abs.
  rewrite -[RHS]IH //.
  congr shift.
  by apply val_inj.
- by rewrite IH1 // IH2.
Qed.

Lemma shift_substv n (k j : 'I_n.+1) (t' : term n) (t : term n.+1) :
  shift k (substv j t' t) =
  substv (lift (lift (fit j) k) j) (shift k t') (shift (lift (fit j) k) t).
Proof.
set h := height t.
have Hh : height t <= h by [].
clearbody h.
elim/lt_wf_ind: h n k j t' t Hh => h IH n k j t' t.
case: t => [i | t | t1 t2] /= Hh.
- case: unliftP => /= [m|] ->; last first.
  + by rewrite unlift_none.
  + case: unliftP => /= [l|].
      move/(f_equal (@nat_of_ord _)) => /=.
      set k' := bump j k.
      rewrite bumpC bumpK.
      move/(can_inj (@bumpK _)) => Hl.
      congr Var.
      exact: val_inj.
    move/lift_inj => /esym /eqP Hj.
    by elim: (negP (neq_lift j m)).
- congr Abs.
  rewrite (IH (height t)) //.
  congr substv.
  + apply val_inj => /=.
    rewrite /bump /= !add1n ltnS.
    case Hj: (j <= k).
      by rewrite !add1n ltnS addnS.
    by rewrite !add0n ltnS addnS.
  + rewrite -shiftC //; congr shift; exact: val_inj.
  + congr shift; apply val_inj => /=; by rewrite -bumpC.
  + by apply/ltP.  
- congr App.
  + apply (IH (height t1)) => //; apply/ltP.
    move: Hh; by rewrite gtn_max => /andP [].
  + apply (IH (height t2)) => //; apply/ltP.
    move: Hh; by rewrite gtn_max => /andP [].
Qed.

Lemma shift_substvC n (k j : 'I_n.+1) (t' : term n) (t : term n.+1) :
  shift k (substv j t' t) =
  substv (lift (fit k) j) (shift k t') (shift (lift (lift ord0 j) k) t).
Proof.
set h := height t.
have Hh : height t <= h by [].
clearbody h.
elim/lt_wf_ind: h n k j t' t Hh => h IH n k j t' t.
case: t => [i | t | t1 t2] /= Hh.
- case: unliftP => /= [m|] -> {i}; last first.
  + case: unliftP => /= [l|] /(f_equal (@nat_of_ord _)) //=.
    rewrite /(bump 0) leq0n add1n /(bump j.+1).
    case Hjk: (j < k).
      rewrite add1n /bump (leqNgt k) ltnNge leq_eqVlt Hjk orbT add0n => /eqP H.
      by elim: (negP (neq_bump j l)).
    rewrite add0n => /eqP H.
    by elim: (negP (neq_bump (bump k j) l)).
  + case: unliftP => /= [l|] /(f_equal (@nat_of_ord _)) /=.
      move=> Hl; congr Var; apply val_inj => /=.
      apply (can_inj (bumpK (bump k j))).
      rewrite -{}Hl /(bump 0) leq0n add1n bumpC bumpK.
      congr bump; rewrite /(bump k) leqNgt /bump.
      case Hjk: (j < k).
        by rewrite add0n leq_eqVlt Hjk orbT.
      by rewrite add1n Hjk.
    rewrite /(bump 0) leq0n add1n /(bump j.+1).
    case Hjk: (j < k).
      rewrite add1n /(bump k) leqNgt Hjk add0n bumpC.
      rewrite /(bump k.+1) ltnNge leq_eqVlt Hjk orbT add0n => /esym /eqP H.
      by elim: (negP (neq_bump j (bump (unbump j k.+1) m))).
    rewrite add0n bumpC => /esym /eqP H.
    by elim: (negP (neq_bump (bump k j) (bump (unbump j k) m))).
- congr Abs.
  rewrite (IH (height t)) //.
  congr substv.
  + apply val_inj => /=; by rewrite /bump /= !add1n ltnS addnS.
  + rewrite -shiftC //; congr shift; exact: val_inj.
  + congr shift; apply val_inj => /=; by rewrite -bumpC.
  + by apply/ltP.
- congr App.
  + apply (IH (height t1)) => //; apply/ltP.
    move: Hh; by rewrite gtn_max => /andP [].
  + apply (IH (height t2)) => //; apply/ltP.
    move: Hh; by rewrite gtn_max => /andP [].
Qed.

Lemma substv_shiftK n j (t : term n) t' : substv j t' (shift j t) = t.
Proof.
elim: t j t' => {n} [n i | n t1 IH | n t1 IH1 t2 IH2] j t' /=.
- by rewrite liftK.
- by rewrite IH.
- by rewrite IH1 IH2.
Qed.

Lemma substvC n (k j : 'I_n.+1) (t1 : term n) (t2 : term n.+1) (t : term n.+2) :
  j <= k ->
  substv k t1 (substv (fit j) t2 t) =
  substv j (substv k t1 t2) (substv (lift ord0 k) (shift j t1) t).
Proof.
set h := height t.
have Hh : height t <= h by [].
clearbody h.
elim/lt_wf_ind: h n k j t1 t2 t Hh => h IH n k j t1 t2.
case => [i | t | t1' t2'] /= Hh Hj.
- have bumpjk : bump j k = k.+1 by rewrite /bump Hj.
  have bump0k : bump 0 k = k.+1 by [].
  case: unliftP => /= [m1|] ->.
    case: unliftP => /= [m2|] ->.
      case: unliftP => /= [m3|].
        case: unliftP => /= [m4|] -> /(f_equal (@nat_of_ord _)) /=.
          rewrite bumpC bumpjk.
          have -> : unbump k j = j.
            by rewrite /unbump ltnNge Hj subn0.
          do 2 move/(can_inj (@bumpK _)).
          move => Hm2; congr Var; exact: val_inj.
        have -> : bump (bump 0 k) j = j.
          by rewrite /bump leq0n ltnNge Hj.
        move=> /esym /eqP Hb.
        by elim: (negP (neq_bump j (bump k m2))).
      move/(f_equal (@nat_of_ord _)) => /=.     
      rewrite bumpC bumpjk => /esym /eqP H.
      by elim: (negP (neq_bump (bump 0 k) (bump (unbump k j) m2))).
    case: unliftP => /= [m2|] /(f_equal (@nat_of_ord _)) /=.
      rewrite bumpjk => /eqP H.
      by elim: (negP (neq_bump (bump 0 k) m2)).
    by rewrite substv_shiftK.
  case: unliftP => /= [m1|] /(f_equal (@nat_of_ord _)) /= Hm1.
    case: unliftP => /= [m2|] /(f_equal (@nat_of_ord _)) //= Hm2.
    move: Hm1.
    rewrite Hm2 bumpC bump0k /(bump k.+1) ltnNge Hj add0n => /eqP H.
    by elim: (negP (neq_bump j (bump (unbump j k.+1) m2))).
  by rewrite Hm1 /bump leq0n ltnn in Hj.
- congr Abs.
  have -> : lift ord0 (fit j) = fit (lift ord0 j).
    exact: val_inj.
  rewrite (IH (height t)) //.
    congr substv.
    + rewrite shift_substvC.
      congr substv.
      congr shift.
      exact: val_inj.
    + congr substv.
      rewrite -shiftC.
      congr shift.
      exact: val_inj.
    + exact: leq0n.
  exact/ltP.
- congr App.
  + rewrite (IH (height t1')) //.
    apply/ltP.
    move: Hh.
    by rewrite gtn_max => /andP [].
  + rewrite (IH (height t2')) //.
    apply/ltP.
    move: Hh.
    by rewrite gtn_max => /andP [].
Qed.

Lemma shift_par n k (t t' : term n) :
  t =>p t' -> shift k t =>p shift k t'.
Proof.
move=> H.
elim: H k => {n t t'} [n i | n t t' H IH | n t1 t2 t1' t2' H1 IH1 H2 IH2
                                         | n t1 t1' t2 t2' H1 IH1 H2 IH2] /= k.
- by constructor.
- by constructor.
- by constructor.
- rewrite shift_substv //.
  have -> : lift (lift ord0 k) ord0 = ord0 by apply val_inj.
  by constructor.
Qed.

Definition eqdep_nat := Eqdep_dec.inj_pair2_eq_dec _ Nat.eq_dec.

Lemma subst_fullpar n k (t1 t1' : term n) t2 t2' :
  t2 =>p t2' -> t1 =>p t1' -> substv k t1 t2 =>p substv k t1' t2'.
Proof.
set h := height t2.
have Hh : height t2 <= h by [].
clearbody h.
elim/lt_wf_ind: h n k t2 Hh t2' t1 t1' => h IH n k t2 Hh t2' t1 t1' H2 H1.
inversion H2; subst.
- rewrite -(eqdep_nat H3) -(eqdep_nat H4) /=.
  case: (unlift k m) => //; by constructor.
- rewrite -(eqdep_nat H) -(eqdep_nat H3) /=.
  constructor.
  apply: (IH (height t)) => //.
    apply/ltP.
    by rewrite -/(height (Abs t)) (eqdep_nat H).
  by apply shift_par.
- rewrite -(eqdep_nat H) -(eqdep_nat H0) /=.
  constructor.
    apply: (IH (height t0)) => //.
    apply/ltP.
    apply (@leq_trans (height (App t0 t3))).
      by rewrite ltnS leq_maxl.
    by rewrite (eqdep_nat H).
  apply: (IH (height t3)) => //.
  apply/ltP.
  apply (@leq_trans (height (App t0 t3))).
    by rewrite ltnS leq_maxr.
  by rewrite (eqdep_nat H).
- rewrite -(eqdep_nat H) -(eqdep_nat H0) /=.
  rewrite [in substv ord0](_ : ord0 = widen_ord (leqnSn n.+1) ord0);
    last exact: val_inj.
  rewrite substvC //.
  constructor.
  + apply: (IH (height t0)) => //.
      apply/ltP.
      apply (@leq_trans (height (App (Abs t0) t3))).
        rewrite /= ltnS.
        by apply ltnW, leq_maxl.
      by rewrite (eqdep_nat H).
    by apply shift_par.
  + apply: (IH (height t3)) => //.
    apply/ltP.
    apply (@leq_trans (height (App (Abs t0) t3))).
      by rewrite ltnS leq_maxr.
    by rewrite (eqdep_nat H).
Qed.

Lemma par_fullpar n (t t' : term n) : t =>p t' -> t' =>p fullpar t.
Proof.
elim=> /= {n t t'} [n k | n t t' H IH | n t1 t2 t1' t2' H1 IH1 H2 IH2
                                      | n t1 t1' t2 t2' H1 IH1 H2 IH2].
- by constructor.
- by constructor.
- destruct t1 => /=.
  + by constructor.
  + destruct t1'; inversion H1; subst.
    constructor.
    * inversion IH1; subst.
      by rewrite -(eqdep_nat H0) -(eqdep_nat H6).
    * by inversion IH2; subst.
  + by constructor.
- exact: subst_fullpar.
Qed.

Lemma refl_par n (t : term n) : t =>p t.
Proof.
elim: t => {n} [n i | n t1 IH | n t1 IH1 t2 IH2] /=; by constructor.
Qed.

Lemma beta1_par n (t t' : term n) : t =>1 t' -> t =>p t'.
Proof.
elim=> /= {n t t'} [n t t' H IH | n t1 t2 t1' H1 IH1
                   | n t1 t2 t2' H2 IH2 | n t1 t2].
- by constructor.
- constructor => //; exact: refl_par.
- constructor => //; exact: refl_par.
- constructor; exact: refl_par.
Qed.

Inductive tr_clos (A : Type) (P : A -> A -> Prop) : A -> A -> Prop :=
| tr_refl : forall x, tr_clos P x x
| tr_step : forall x y z, P x y -> tr_clos P y z -> tr_clos P x z.

Lemma tr_clos_trans A P y x z :
  @tr_clos A P x y -> tr_clos P y z -> tr_clos P x z.
Proof. elim: x y / => // x x1 y Hx Hx1 IH /IH; exact: tr_step. Qed.

Lemma lift_tr_clos A B f (P : A -> A -> Prop) (P' : B -> B -> Prop) x y :
  (forall x y, P x y -> P' (f x) (f y)) ->
  tr_clos P x y -> tr_clos P' (f x) (f y).
Proof.
move=> Hlf.
elim: x y/.
- by constructor.
- move=> x y z Pxy _; by apply/tr_step/Hlf.
Qed.

Arguments tr_clos_trans {A} {P}.
Arguments lift_tr_clos {A} {B}.

Notation "t =>* t'" := (tr_clos (@beta1 _) t t')
                       (at level 70, no associativity).

Lemma par_beta n (t t' : term n) : t =>p t' -> t =>* t'.
Proof.
elim=> /= {n t t'} [n k | n t t' H IH | n t1 t2 t1' t2' H1 IH1 H2 IH2
                                      | n t1 t1' t2 t2' H1 IH1 H2 IH2].
- by constructor.
- apply (lift_tr_clos (@Abs n) (@beta1 _)) => // *; by constructor.
- apply (tr_clos_trans (App t1 t2')).
    apply (lift_tr_clos (App t1) (@beta1 _)) => // *; by constructor.
  apply (lift_tr_clos (@App n ^~ t2') (@beta1 _)) => // *; by constructor.
- apply (tr_clos_trans (App (Abs t1) t2')).
    apply (lift_tr_clos (App (Abs t1)) (@beta1 _)) => // *; by constructor.
  apply (tr_clos_trans (App (Abs t1') t2')).
    apply (lift_tr_clos (fun t1 => App (Abs t1) t2') (@beta1 _)) => // *.
    by do! constructor.
  apply/tr_step/tr_refl; by constructor.
Qed.
