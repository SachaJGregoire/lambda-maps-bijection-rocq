(* Imports *)
From mathcomp Require Import
  fintype perm ssreflect ssrfun ssrbool eqtype all_ssreflect.

(* Definitions *)
(* Linear Lambda Terms (with pairwise-unique free variables) *)
Inductive llambda : nat -> Type :=                                (* Linear lambda terms *)
| LVar            : llambda 1                                     (* Variable *)
| LApp {k m}      : llambda k -> llambda m -> llambda (k+m)       (* Application *)
| LAbs {k}        : 'I_(S k) -> llambda (S k) -> llambda k        (* Abstraction *)
.

(* Rooted Trivalent Maps (with boundary) *)
(* Reachable from root *)
Inductive reachable {T : finType} (v e : T -> T) (y : T) : T -> Prop :=
| reach_r : (reachable v e y) y
| reach_v : forall x, (reachable v e y) x -> (reachable v e y) (v x)
| reach_e : forall x, (reachable v e y) x -> (reachable v e y) (e x).

Lemma reachrefl   {T : finType} v e (x : T) : reachable v e x x.
Proof. by apply reach_r. Qed.

Lemma reachtrans  {T : finType} (y : T) v e (x z : T) : 
  reachable v e x y -> reachable v e y z -> reachable v e x z.
Proof.
move => Exy Eyz.
elim: Eyz => [| w _ IH | w _ IH] //=.
+ by apply reach_v.
+ by apply reach_e.
Qed.

Lemma reachsym    {T : finType} v e
  (v3 : forall x, v (v (v x)) = x) (e2 : forall x, e (e x) = x) (x y : T) :
  reachable v e x y -> reachable v e y x.
Proof.
move => Exy. elim: Exy => [| w _ IH | w _ IH].
apply reach_r.
apply: (reachtrans w).
  rewrite -{2}(v3 w). apply reach_v. apply reach_v. apply reach_r. apply IH.
apply: (reachtrans w).
  rewrite -{2}(e2 w). apply reach_e. apply reach_r. apply IH.
Qed.

(* Transitivity *)
Definition transitive {T : finType} (v e : T -> T) (r : T) : Prop :=
  forall x, (reachable v e r) x.

(*CHOICE : vtrivalent. Contrapositive works also. *)
Record rtmap (k : nat) : Type := {                            (* Rooted trivalent maps *)
  T             : finType;                                    (* Dart type *)
  v             : T -> T;                                     (* Vertex permutation *)
  e             : T -> T;                                     (* Edge permutation *)
  boundary      : 'I_(S k) -> T;                              (* Root and boundary darts *)
  boundary_inj  : injective boundary;                         (* Exactly k boundary darts *)
  vboundary     : forall i, v (boundary i) = (boundary i);    (* Boundarys are univalent *)
  vtrivalent    : forall x, v x = x ->                        (* Only root and boundarys *)
                            exists i, x = boundary i;             (* are univalent *)
  v3            : forall x, v (v (v x)) = x;                  (* Vertices have degree 1 or 3 *)
  eall          : forall x, e x <> x;                         (* Every dart is in an edge *)
  e2            : forall x, e (e x) = x;                      (* Edges have degree 2 *)
  trans         : transitive v e (boundary ord0);             (* Darts are transitive *)
}.



(* Helper Functions *)
Definition root {k} (A : rtmap k) := A.(boundary k) ord0.

Definition square {T} (v : T -> T) : T -> T := fun x => v (v x).

Lemma vK {k} (A : rtmap k) : let v := A.(v k) in cancel v (square v).
Proof. move => v x. exact: A.(v3 k). Qed.

Lemma vP {k} (A : rtmap k) : let v := A.(v k) in cancel (square v) v.
Proof. move => v x. exact: A.(v3 k). Qed.

Lemma v_bij {k} (A : rtmap k) : bijective A.(v k).
Proof. exists (square (v k A)); [apply vK | apply vP]. Qed. 

Lemma v_inj {k} (A : rtmap k) : injective A.(v k).
Proof. apply (can_inj (vK A)). Qed.

Lemma v_boundary {k i} (A : rtmap k) : forall x,
  A.(v k) x = boundary k A i -> x = boundary k A i.
Proof.
move => x E.
assert (v k A (boundary k A i) = boundary k A i). by rewrite vboundary.
rewrite -H in E. by apply v_inj in E.
Qed.


Lemma eK {k} (A : rtmap k) : cancel A.(e k) A.(e k).
Proof. move => x. by rewrite e2. Qed.

Lemma e_bij {k} (A : rtmap k) : bijective A.(e k).
Proof. exists (e k A); [apply eK | apply eK]. Qed.


Lemma split_inj {m n} : injective (@split m n).
Proof. by apply: (can_inj (@splitK m n)). Qed.

Lemma root_eq {k} (A : rtmap k) : root A == root A. Proof. done. Qed. 

Lemma boundary_eq {k i} (A : rtmap k) : boundary k A i == boundary k A i.
Proof. done. Qed.

Lemma root_boundary_neq {k i} (A : rtmap k): 
(root A == boundary k A (lift ord0 i)) = false.
Proof. apply/eqP => H. by apply boundary_inj in H. Qed.

Lemma boundary_root_neq {k i} (A : rtmap k): 
(boundary k A (lift ord0 i) == root A) = false.
Proof. apply/eqP => H. by apply boundary_inj in H. Qed.





(* Coercing linear lambda terms into rooted trivalent maps *)
Program Definition rtVar : rtmap 1 :=
{|
  T             := (unit + unit) %type;
  v             := id;
  e             := (fun x =>
    match x with  
    | inl tt  => inr tt
    | inr tt  => inl tt
    end);
  boundary      := (fun a =>
    match a with
    | Ordinal 0 _ => inl tt
    | _Ordinal1   => inr tt 
    end);
  boundary_inj  := _;
  vboundary     := _;
  vtrivalent    := _;
  v3            := _;
  eall          := _;
  e2            := _;
  trans         := _;
|}.
Next Obligation. (* boundary_inj *)
move => x y.
case x => [[| [|x_n]] x_pr]; case y => [[| [|y_n]] y_pr] //=;
move => H; by apply val_inj.
Qed.
(* automatic proof: vboundary *)
Next Obligation. (* vtrivalent *)
case x => [[]|[]]. by exists ord0. by exists (ordS ord0).
Qed.
(* automatic proof: v3 *)
Next Obligation. (* eall *)
by case x => [[]|[]].
Qed.
Next Obligation. (* e2 *)
by case x => [[]|[]].
Qed.
Next Obligation. (* trans *)
set f_e := (fun x : unit + unit =>
   match x as x' return (x' = x -> unit + unit) with
   | inl s => match s as s0 return (inl s0 = x -> unit + unit) with
              | tt => fun=> inr tt
              end
   | inr s => match s as s0 return (inr s0 = x -> unit + unit) with
              | tt => fun=> inl tt
              end
   end erefl).
case => [[]|[]]. apply reach_r.
have Ee: (inr tt = f_e (inl tt)) by done. rewrite Ee.
apply reach_e. apply reach_r.
Qed.



Program Definition rtApp {k j} (A : rtmap k) (B : rtmap j) : rtmap (k+j) :=
{|
  T             := (unit + (unit + (A.(T k) + B.(T j))))  %type;
  v             := (fun x =>
    match x with
    (* Root maps to itself *)
    | inl tt            => inl tt
    (* New boundary maps to root of P *)
    | inr (inl tt)      => inr (inr (inl (root A)))
    | inr (inr (inl y)) =>
      (* Root of P maps to root of Q *)
      if y == root A then inr (inr (inr (root B)))
      (* Everything else maps as usual *)
      else inr (inr (inl (A.(v k) y)))
    | inr (inr (inr z)) => 
      (* Root of Q maps to the new boundary *)
      if z == root B then inr (inl tt)
      (* Everything else maps as usual *)
      else inr (inr (inr (B.(v j) z)))
    end);
  e             := (fun x =>
    match x with
    (* Root maps to new boundary *)
    | inl tt            => inr (inl tt)
    (* New boundary maps to new root *)
    | inr (inl tt)      => inl tt
    (* Otherwise, map to same place as before *)
    | inr (inr (inl y)) => inr (inr (inl (A.(e k) y)))
    | inr (inr (inr z)) => inr (inr (inr (B.(e j) z)))
    end);
  boundary      := (fun a =>
    match unlift ord0 a with
    | None    => inl tt
    | Some b  => match split b with
      | inl iA            => inr (inr (inl (A.(boundary k) (lift ord0 iA))))
      | inr iB            => inr (inr (inr (B.(boundary j) (lift ord0 iB))))
      end
    end);
  boundary_inj  := _;
  vboundary     := _;
  vtrivalent    := _;
  v3            := _;
  eall          := _;
  e2            := _;
  trans         := _;
|}.
Next Obligation. (* boundary_inj *)
move => x y.
case (unliftP ord0 x) => [vx Ex | vx]; case (unliftP ord0 y) => [vy Ey | vy] //=.
case (splitP vx) => [vxL | vxR] Evx; case (splitP vy) => [vyL | vyR] Evy //=;
  move => H; injection H => Eb; apply boundary_inj in Eb;
  apply lift_inj in Eb; rewrite Eb -Evy in Evx;
  rewrite Ex Ey; apply val_inj; unfold lift; simpl; by rewrite Evx.
by case (splitP vx). by case (splitP vy). by rewrite vx vy.
Qed.
Next Obligation. (* vboundary *)
case (unliftP ord0 i) => [vi Ei | vi] //=. case (splitP vi) => [viL | viR] Evi.
assert (boundary k A (lift ord0 viL) != root A). rewrite inj_eq. 
  by apply (neq_lift ord0 viL). apply A.(boundary_inj k).
  rewrite (negPf H). by rewrite (A.(vboundary k) (lift ord0 viL)).
assert (boundary j B (lift ord0 viR) != root B). rewrite inj_eq. 
  by apply (neq_lift ord0 viR). apply B.(boundary_inj j).
  rewrite (negPf H). by rewrite (B.(vboundary j) (lift ord0 viR)).
Qed.
Next Obligation. (* vtrivalent *)
case Ex: x => [[] | [[] | [y|z]]] in H.
exists ord0. by rewrite unlift_none. done.
case Ea: (y == root A); rewrite Ea in H. done. injection H => Ey.
  move: (A.(vtrivalent k) y Ey) => [i Ei].
  (* exists i: unlift, unsplit, lift *)
  case (unliftP ord0 i) => [vi Evi | vi] //=; simpl in vi.
  +
  case (unsplit (inl vi): 'I_(k+j)) eqn : Evii.
  case (lift ord0 (Ordinal (n:=k + j) (m:=m) i0)) eqn : Eviii.
  move: (f_equal (unlift ord0) Eviii) => Hiii. rewrite liftK in Hiii.
  exists (Ordinal (n:=(k + j).+1) (m:=m0) i1). rewrite -Hiii.
  move: (f_equal split Evii) => Hii. rewrite unsplitK in Hii. rewrite -Hii.
  by rewrite Ex Ei Evi.
  + move: Ea. by rewrite Ei vi eqxx.
case Eb: (z == root B); rewrite Eb in H. done. injection H => Ez.
  move: (B.(vtrivalent j) z Ez) => [i Ei].
  (* exists i: unlift, unsplit, lift *)
  case (unliftP ord0 i) => [vi Evi | vi] //=; simpl in vi.
  +
  case (unsplit (inr vi): 'I_(k+j)) eqn : Evii.
  case (lift ord0 (Ordinal (n:=k + j) (m:=m) i0)) eqn : Eviii.
  move: (f_equal (unlift ord0) Eviii) => Hiii. rewrite liftK in Hiii.
  exists (Ordinal (n:=(k + j).+1) (m:=m0) i1). rewrite -Hiii.
  move: (f_equal split Evii) => Hii. rewrite unsplitK in Hii. rewrite -Hii.
  by rewrite Ex Ei Evi.
  + move: Eb. by rewrite Ei vi eqxx. 
Qed.
Next Obligation. (* v3 *)
case Ex: x => [[] | [[] | [y|z]]] //=.
by rewrite !root_eq.
case Ey : (y == root A); move/eqP: Ey => Ey.
- rewrite root_eq. by rewrite Ey.
- move: (contra_not (v_boundary A y) Ey) => Evy. rewrite (introF eqP Evy).
  move: (contra_not (v_boundary A (v k A y)) Evy) => Evvy. rewrite (introF eqP Evvy).
  by rewrite A.(v3 k).
case Ez : (z == root B); move/eqP: Ez => Ez.
- rewrite root_eq. by rewrite Ez.
- move: (contra_not (v_boundary B z) Ez) => Evz. rewrite (introF eqP Evz).
  move: (contra_not (v_boundary B (v j B z)) Evz) => Evvz. rewrite (introF eqP Evvz).
  by rewrite B.(v3 j).
Qed.
Next Obligation. (* eall *)
case Ex: x => [[] | [[] | [y|z]]] //=; move => H; injection H; by apply eall.
Qed.
Next Obligation. (* e2 *)
case Ex: x => [[] | [[] | [y|z]]] //=; by rewrite e2.
Qed.
Next Obligation. (* trans *)
rewrite unlift_none.
set f_v := (fun x : unit + (unit + (T k A + T j B)) =>
   match x as x' return (x' = x -> unit + (unit + (T k A + T j B))) with
   | inl s =>
       match s as s0 return (inl s0 = x -> unit + (unit + (T k A + T j B))) with
       | tt => fun=> inl tt
       end
   | inr s =>
       match s as s0 return (inr s0 = x -> unit + (unit + (T k A + T j B))) with
       | inl s0 =>
           match s0 as s1 return (inr (inl s1) = x -> unit + (unit + (T k A + T j B))) with
           | tt => fun=> inr (inr (inl (root A)))
           end
       | inr s0 =>
           match s0 as s1 return (inr (inr s1) = x -> unit + (unit + (T k A + T j B))) with
           | inl y =>
               fun=> (if y == root A
                      then inr (inr (inr (root B)))
                      else inr (inr (inl (v k A y))))
           | inr z => fun=> (if z == root B then inr (inl tt) else inr (inr (inr (v j B z))))
           end
       end
   end erefl).
set f_e := (fun x : unit + (unit + (T k A + T j B)) =>
   match x as x' return (x' = x -> unit + (unit + (T k A + T j B))) with
   | inl s =>
       match s as s0 return (inl s0 = x -> unit + (unit + (T k A + T j B))) with
       | tt => fun=> inr (inl tt)
       end
   | inr s =>
       match s as s0 return (inr s0 = x -> unit + (unit + (T k A + T j B))) with
       | inl s0 =>
           match s0 as s1 return (inr (inl s1) = x -> unit + (unit + (T k A + T j B))) with
           | tt => fun=> inl tt
           end
       | inr s0 =>
           match s0 as s1 return (inr (inr s1) = x -> unit + (unit + (T k A + T j B))) with
           | inl y => fun=> inr (inr (inl (e k A y)))
           | inr z => fun=> inr (inr (inr (e j B z)))
           end
       end
   end erefl).
move => x. case Ex: x => [[] | [[] | [y|z]]] //=. apply reach_r.
+
have Ee: (inr (inl tt) = f_e (inl tt)) by done. rewrite Ee.
apply reach_e. apply reach_r.
+ (* inr (inr (inl A))) *)
(* Establish reachability of (Root A) *)
have ReachRootA : reachable f_v f_e (inl tt) (inr (inr (inl (root A)))).
have Ev: (inr (inr (inl (root A))) = f_v (inr (inl tt))) by done. rewrite Ev.
apply reach_v. have Ee: ((inr (inl tt) = f_e (inl tt))) by done. rewrite Ee.
apply reach_e. apply reach_r.
(* Lifting Lemma *)
have LiftA: forall z, reachable (v k A) (e k A) (root A) z ->
                      reachable f_v f_e (inl tt) (inr (inr (inl z))).
{
move => z Ez. induction Ez as [| u Eu IH | u Eu IH]. done.
+ (* Vertex Step: We reached u, and in A we step to v_A u *)
  case Ru: (u == root A).
  - (* u == Root A. The functions diverge here *)
  move/eqP: Ru => Ru.
  have Ev: (inr (inr (inl (v k A u))) = f_v (inr (inl tt))) by rewrite Ru vboundary.
  rewrite Ev. apply reach_v.
  have Ee: (inr (inl tt) = f_e (inl tt)) by done.
  rewrite Ee. apply reach_e. apply reach_r.
  - (* u != Root A. The functions are identical *)
  have Ev: (inr (inr (inl (v k A u))) = f_v (inr (inr (inl u)))).
  unfold f_v. by rewrite Ru. rewrite Ev. by apply reach_v.
+ (* Edge Step: We reached u, and in A we step to e_A u *)
  have Ee: (inr (inr (inl (e k A u))) = f_e (inr (inr (inl u)))) by done.
  rewrite Ee. by apply reach_e.
}
apply LiftA. by apply trans.
+ (* inr (inr (inr B))) *)
(* Establish reachability of (Root A) *)
have ReachRootA : reachable f_v f_e (inl tt) (inr (inr (inl (root A)))).
have Ev: (inr (inr (inl (root A))) = f_v (inr (inl tt))) by done. rewrite Ev.
apply reach_v. have Ee: ((inr (inl tt) = f_e (inl tt))) by done. rewrite Ee.
apply reach_e. apply reach_r.
(* Establish reachability of (Root B) *)
have ReachRootB : reachable f_v f_e (inl tt) (inr (inr (inr (root B)))).
have Ev: (inr (inr (inr (root B))) = f_v (inr (inr (inl (root A))))).
  unfold f_v. by rewrite root_eq.
rewrite Ev. by apply reach_v.
(* Lifting Lemma *)
have LiftB: forall y, reachable (v j B) (e j B) (root B) y ->
                      reachable f_v f_e (inl tt) (inr (inr (inr y))).
{
move => y Ey. induction Ey as [| u Eu IH | u Eu IH]. done.
+ (* Vertex Step: We reached u, and in A we step to v_B u *)
  case Ru: (u == root B).
  - (* u == Root B. The functions diverge here *)
  move/eqP: Ru => Ru.
  have Ev: (inr (inr (inr (v j B u))) = f_v (inr (inr (inl (root A))))).
    unfold f_v. by rewrite Ru vboundary root_eq.
  rewrite Ev. by apply reach_v.
  - (* u != Root B. The functions are identical *)
  have Ev: (inr (inr (inr (v j B u))) = f_v (inr (inr (inr u)))).
  unfold f_v. by rewrite Ru. rewrite Ev. by apply reach_v.
+ (* Edge Step: We reached u, and in A we step to e_B u *)
  have Ee: (inr (inr (inr (e j B u))) = f_e (inr (inr (inr u)))) by done.
  rewrite Ee. by apply reach_e.
}
apply LiftB. by apply trans.
Qed.



Program Definition rtAbs {k} (b : 'I_(S k)) (A : rtmap (S k)) : rtmap k :=
let removed_boundary := boundary (S k) A (lift ord0 b) in
{|
  T             := (unit + (unit +  A.(T (S k)))) %type;
  v             := (fun x =>
    match x with
    (* Root maps to itself *)
    | inl tt        => inl tt
    (* New boundary maps to the previous root *)
    | inr (inl tt)  => inr (inr (root A))
    | inr (inr y)   => 
      (* Previous root maps to removed boundary *)
      if y == root A            then  inr (inr removed_boundary)  else
      (* Removed boundary maps to new boundary *)
      if y == removed_boundary  then  inr (inl tt)                else
      (* Everything else maps as usual *)
                                      inr (inr (v (S k) A y))
    end);
  e             := (fun x =>
    match x with
    (* Root maps to new boundary *)
    | inl tt        => inr (inl tt)
    (* New boundary maps to new root *)
    | inr (inl tt)  => inl tt
    (* Otherwise, map to same place as before *)
    | inr (inr y)   => inr (inr (e (S k) A y))
    end);
  boundary      := (fun a =>
    if a == ord0 then inl tt else
                      inr (inr (A.(boundary (S k)) (lift (lift ord0 b) a))));
  boundary_inj  := _;
  vboundary     := _;
  vtrivalent    := _;
  v3            := _;
  eall          := _;
  e2            := _;
  trans         := _;
|}.
Next Obligation. (* boundary_inj *)
move => x y.
case Ex: (x == ord0); move/eqP: Ex => Ex; case Ey: (y == ord0); move/eqP: Ey => Ey //=.
by rewrite Ex Ey.
move => H. injection H => Eb. apply (boundary_inj (S k) A) in Eb.
move: (f_equal (unlift (lift ord0 b)) Eb). rewrite !liftK. 
move => Exy. by injection Exy.
Qed.
Next Obligation. (* vboundary *)
case Ei: (i == ord0); move/eqP: Ei => Ei //=.
move: (neq_lift (lift ord0 b) i) => Eb.
assert (boundary k.+1 A (lift (lift ord0 b) i) <> root A). move/eqP => Hi.
rewrite inj_eq in Hi.
assert (lift (lift ord0 b) i = lift (lift ord0 b) ord0).
rewrite (eqP Hi). unfold lift. by apply val_inj.
apply lift_inj in H. by rewrite H in Ei. apply A.(boundary_inj (S k)).
move/eqP: H => Hb. rewrite (negPf Hb).
assert (boundary k.+1 A (lift ord0 b) != boundary k.+1 A (lift (lift ord0 b) i)).
rewrite inj_eq. done. apply (boundary_inj (S k) A). rewrite eq_sym (negPf H).
by rewrite (A.(vboundary (S k)) (lift (lift ord0 b) i)).
Qed.
Next Obligation. (* vtrivalent *)
case Ex: x => [[] | [[] | y]] in H.
by exists ord0. done.
case Er: (y == root A) in H; move/eqP: Er => Er.
injection H => Ey. rewrite Er in Ey. apply boundary_inj in Ey.
move: (neq_lift ord0 b). by rewrite Ey.
case Eb: (y == boundary k.+1 A (lift ord0 b)) in H; move/eqP: Eb => Eb. done.
injection H => Ey. move: (vtrivalent k.+1 A y Ey) => [i Ei].
have Ei0: i <> ord0. move => E. by rewrite Ei E in Er.
case (unliftP (lift ord0 b) i) => [j Ej | Ej].
case E1: (j == ord0); move/eqP: E1 => E1. rewrite E1 in Ej.
  unfold lift in Ej. unfold bump in Ej. simpl in Ej.
  assert (i = ord0). rewrite Ej. apply val_inj. done. done.
exists j. move/eqP: E1 => E1. by rewrite (negPf E1) Ex Ei Ej.
by rewrite Ei Ej in Eb.
Qed.
Next Obligation. (* v3 *)
case Ex: x => [[] | [[] | y]] //=.
by rewrite eq_refl boundary_root_neq eq_refl.
case Er : (y == root A); move/eqP: Er => Er.
by rewrite boundary_root_neq eq_refl Er.
case Eb : (y == boundary k.+1 A (lift ord0 b)); move/eqP: Eb => Eb.
by rewrite eq_refl Eb.
move: (contra_not (v_boundary A y) Eb) => Ebb. rewrite (introF eqP Ebb).
move: (contra_not (v_boundary A y) Er) => Err. rewrite (introF eqP Err).
move: (contra_not (v_boundary A (v k.+1 A y)) Ebb) => Eb3. rewrite (introF eqP Eb3).
move: (contra_not (v_boundary A (v k.+1 A y)) Err) => Er3. rewrite (introF eqP Er3).
by rewrite v3.
Qed.
Next Obligation. (* eall *)
case Ex: x => [[] | [[] | y]] //=; move => H; injection H; by apply eall.
Qed.
Next Obligation. (* e2 *)
case Ex: x => [[] | [[] | y]] //=; by rewrite e2.
Qed.
Next Obligation. (* trans *)
set f_v := (fun x : unit + (unit + T k.+1 A) =>
   match x as x' return (x' = x -> unit + (unit + T k.+1 A)) with
   | inl s =>
       match s as s0 return (inl s0 = x -> unit + (unit + T k.+1 A)) with
       | tt => fun=> inl tt
       end
   | inr s =>
       match s as s0 return (inr s0 = x -> unit + (unit + T k.+1 A)) with
       | inl s0 =>
           match s0 as s1 return (inr (inl s1) = x -> unit + (unit + T k.+1 A)) with
           | tt => fun=> inr (inr (root A))
           end
       | inr y =>
           fun=> (if y == root A
                  then inr (inr (boundary k.+1 A (lift ord0 b)))
                  else
                   if y == boundary k.+1 A (lift ord0 b)
                   then inr (inl tt)
                   else inr (inr (v k.+1 A y)))
       end
   end erefl).
set f_e := (fun x : unit + (unit + T k.+1 A) =>
   match x as x' return (x' = x -> unit + (unit + T k.+1 A)) with
   | inl s =>
       match s as s0 return (inl s0 = x -> unit + (unit + T k.+1 A)) with
       | tt => fun=> inr (inl tt)
       end
   | inr s =>
       match s as s0 return (inr s0 = x -> unit + (unit + T k.+1 A)) with
       | inl s0 =>
           match s0 as s1 return (inr (inl s1) = x -> unit + (unit + T k.+1 A)) with
           | tt => fun=> inl tt
           end
       | inr y => fun=> inr (inr (e k.+1 A y))
       end
   end erefl).
move => x. case Ex: x => [[] | [[] | y]] //=. apply reach_r.
+
have Ee: (inr (inl tt) = f_e (inl tt)) by done. rewrite Ee.
apply reach_e. apply reach_r.
+ (* inr (inr y)) *)
(* Establish reachability of (Root A) *)
have ReachRootA : reachable f_v f_e (inl tt) (inr (inr (root A))).
have Ev: inr (inr (root A)) = f_v (inr (inl (tt))) by done.
rewrite Ev. apply reach_v.
have Ee: ((inr (inl tt) = f_e (inl tt))) by done.
rewrite Ee. apply reach_e. apply reach_r.
(* Lifting Lemma *)
have LiftA: forall z, reachable (v k.+1 A) (e k.+1 A) (root A) z ->
                      reachable f_v f_e (inl tt) (inr (inr z)).
{
move => z Ez. induction Ez as [| u Eu IH | u Eu IH]. done.
+ (* Vertex Step: We reached u, and in A we step to v_A u *)
  - (* u == removed_boundary *)
  case Bu: (u == boundary (S k) A (lift ord0 b)).
  move/eqP: Bu => Bu.
  have Ev: inr (inr (v k.+1 A u)) = f_v (inr (inr (root A))).
    unfold f_v. by rewrite eq_refl Bu vboundary.
  rewrite Ev. by apply reach_v.
 case Ru: (u == root A).
  - (* u == Root A. The functions diverge here *)
  move/eqP: Ru => Ru.
  have Ev: inr (inr (v k.+1 A u)) = f_v (inr (inl tt)) by rewrite Ru vboundary.
  rewrite Ev. apply reach_v.
  have Ee: (inr (inl tt) = f_e (inl tt)) by done.
  rewrite Ee. apply reach_e. apply reach_r.
  - (* Otherwise. The functions are identical *)
  have Ev: (inr (inr (v k.+1 A u)) = f_v (inr (inr u))).
  unfold f_v. by rewrite Bu Ru. rewrite Ev. by apply reach_v.
+ (* Edge Step: We reached u, and in A we step to e_A u *)
  have Ee: (inr (inr (e k.+1 A u)) = f_e (inr (inr u))) by done.
  rewrite Ee. by apply reach_e.
}
apply LiftA. by apply trans.
Qed.

(* Final construction *)
Fixpoint llambda_to_rtmap {k} (term : llambda k) : rtmap k :=
match term with
| LVar          => rtVar
| LApp p q P Q  => rtApp   (llambda_to_rtmap P) (llambda_to_rtmap Q)
| LAbs k a P    => rtAbs a (llambda_to_rtmap P)
end
.





Record isomorphism {k l} (A : rtmap k) (B : rtmap l) := Isomorphism {
  phi   :> T k A -> T l B;
  keq   : k = l;
  phiV  : forall x, phi (v k A x) = v l B (phi x);
  phiE  : forall x, phi (e k A x) = e l B (phi x);
  phiB  : forall i, phi (boundary k A i) = boundary l B (cast_ord (f_equal S keq) i)
}.
Definition isomorphic {k l} (A : rtmap k) (B : rtmap l) := inhabited (isomorphism A B).

Lemma isorefl {k} (A : rtmap k) : isomorphic A A.
Proof. apply inhabits. refine {|phi:=id;keq:=erefl|}. done. done.
move => i. by rewrite cast_ord_id.
Qed.

(* Symmetry requires an inverse *)

Lemma isotrans {k l m} (A : rtmap k) (B : rtmap l) (C : rtmap m):
  isomorphic A B -> isomorphic B C -> isomorphic A C.
Proof.
Check phi.
move => [isoAB] [isoBC]. apply inhabits.
refine {| phi := phi B C isoBC \o phi A B isoAB;
          keq := etrans (keq A B isoAB) (keq B C isoBC)|}.
move => x. by rewrite /comp !phiV.
move => x. by rewrite /comp !phiE.
move => i. rewrite /comp !phiB. congr boundary. by apply val_inj.
Qed.

(* Testing Grounds *)
Definition triv_gmap : rtmap 1 := llambda_to_rtmap LVar.
Section TrivialExample.
Definition ord2_1 : 'I_2 := Ordinal (n:=2) (m:=1) (ltnSn 1).
Lemma ord2_enum (j : 'I_2) : j = ord0 \/ j = ord2_1.
Proof.
case: j => n pf. case: (n) (pf) => [|[|?]] //=;
[left | right]; by apply val_inj.
Qed.
Definition darts_tr := 'I_2.
Definition v_tr (i : darts_tr) : darts_tr := id i.
Definition e_tr (i : darts_tr) : darts_tr :=
  if i == ord0 then ord2_1 else ord0.
Definition boundary_tr (k : 'I_2) : darts_tr := id k.
Program Definition rtmap_tr : rtmap 1 := {|
  T := darts_tr;
  v := v_tr;
  e := e_tr;
  boundary := boundary_tr;
  boundary_inj := _;
  vboundary := _;
  vtrivalent := _;
  v3 := _;
  eall := _;
  e2 := _;
  trans := _
|}.
Next Obligation. (* boundary_inj *)
move => x y.
case x => [[| [|x_n]] x_pr]; case y => [[| [|y_n]] y_pr] //=;
move => H; by apply val_inj.
Qed.
(* automatic proof: vboundary *)
Next Obligation. (* vtrivalent *)
by exists x.
Qed.
(* automatic proof: v3 *)
Next Obligation. (* eall *)
case (ord2_enum x) => Ex; by rewrite Ex.
Qed.
Next Obligation. (* e2 *)
case (ord2_enum x) => Ex; by rewrite Ex.
Qed.
Next Obligation. (* trans *)
move => x. case (ord2_enum x) => Ex; rewrite Ex.
apply reach_r.
have Ee: (ord2_1 = e_tr ord0) by done. rewrite Ee.
apply reach_e. apply reach_r.
Qed.
Lemma triv_iso : isomorphic triv_gmap rtmap_tr.
set phi : T 1 triv_gmap -> T 1 rtmap_tr := fun x => match x with
  | inl tt => ord0
  | inr tt => ord2_1
  end.
apply inhabits. refine {|phi:=phi;keq:=erefl|}.
by case => [[]|[]].
by case => [[]|[]].
move => i. case (ord2_enum i) => Ei; rewrite Ei;
by apply val_inj.
Qed.
End TrivialExample.

Definition id_term : llambda 0 := LAbs ord0 LVar.
Definition id_map : rtmap 0 := llambda_to_rtmap id_term.
Section IdentityExample.
Definition ord4_1 : 'I_4 := Ordinal (n:=4) (m:=1) (ltnSn 1).
Definition ord4_2 : 'I_4 := Ordinal (n:=4) (m:=2) (ltnSn 2).
Definition ord4_3 : 'I_4 := Ordinal (n:=4) (m:=3) (ltnSn 3).
Lemma ord4_enum (j : 'I_4) : j = ord0 \/ j = ord4_1 \/ j = ord4_2 \/ j = ord4_3.
Proof.
case: j => n pf. case: (n) (pf) => [|[|[|[|?]]]] //=;
[left | right;left | right;right;left | right;right;right]; by apply val_inj.
Qed.
Definition darts_id := 'I_4.
Definition v_id (i : darts_id) : darts_id :=
  if i == ord0    then ord0   else
  if i == ord4_1  then ord4_2 else
  if i == ord4_2  then ord4_3 else  
  if i == ord4_3  then ord4_1 else ord0.
Definition e_id (i : darts_id) : darts_id :=
  if i == ord0    then ord4_1 else
  if i == ord4_1  then ord0   else
  if i == ord4_2  then ord4_3 else
  if i == ord4_3  then ord4_2 else ord0.
Definition boundary_id (k : 'I_1) : darts_id := ord0.
Program Definition rtmap_id : rtmap 0 := {|
  T := darts_id;
  v := v_id;
  e := e_id;
  boundary := boundary_id;
  boundary_inj := _;
  vboundary := _;
  vtrivalent := _;
  v3 := _;
  eall := _;
  e2 := _;
  trans := _
|}.
Next Obligation. (* boundary_inj *)
move => x y.
case x => [[| [|x_n]] x_pr]; case y => [[| [|y_n]] y_pr] //=;
move => H; by apply val_inj.
Qed.
(* automatic proof: vboundary *)
Next Obligation. (* vtrivalent *)
exists ord0. unfold boundary_id.
case (ord4_enum x) as [Ex|[Ex|[Ex|Ex]]]; try done;
by rewrite Ex in H.
Qed.
Next Obligation. (* v3 *)
case (ord4_enum x) as [Ex|[Ex|[Ex|Ex]]]; by rewrite Ex.
Qed.
Next Obligation. (* eall *)
case (ord4_enum x) as [Ex|[Ex|[Ex|Ex]]]; by rewrite Ex.
Qed.
Next Obligation. (* e2 *)
case (ord4_enum x) as [Ex|[Ex|[Ex|Ex]]]; by rewrite Ex.
Qed.
Next Obligation. (* trans *)
have Ee: (ord4_1 = e_id ord0) by done.
have Ev2: (ord4_2 = v_id ord4_1) by done.
have Ev3: (ord4_3 = v_id ord4_2) by done.
move => x. case (ord4_enum x) as [Ex|[Ex|[Ex|Ex]]]; rewrite Ex.
+
apply reach_r.
+
rewrite Ee. apply reach_e. apply reach_r.
+
rewrite Ev2. apply reach_v.
rewrite Ee. apply reach_e. apply reach_r.
+
rewrite Ev3. apply reach_v.
rewrite Ev2. apply reach_v.
rewrite Ee. apply reach_e. apply reach_r.
Qed.
Lemma id_iso : isomorphic id_map rtmap_id.
set phi : T 0 id_map -> T 0 rtmap_id := fun x => match x with
  | inl tt        => ord0
  | inr (inl tt)  => ord4_1
  | inr (inr y)   => match y with
    | inl tt => ord4_2
    | inr tt => ord4_3
    end
  end.
apply inhabits. refine {|phi:=phi;keq:=erefl|}.
+
case => [[] | [[] | y]] //=; case y => [[] | []] //=.
+
case => [[] | [[] | y]] //=; case y => [[] | []] //=.
+
move => i. by rewrite ord1.
Qed.
End IdentityExample.





Lemma Tneq0 {k} : forall (A : rtmap k),
  #|T k A| <> 0.
Proof.
Search (#|_| = 0).
move => A H.
move: (boundary k A ord0) => x.
by move: (fintype0 x).
Qed.

Lemma Tneq1 {k} : forall (A : rtmap k),
  #|T k A| <> 1.
Proof.
Search (#|_| = 1).
move => A H.
move: (fintype1 H) => [x Ex].
by move: (eall k A x).
Qed.

Lemma Tgeq2 {k} : forall (A : rtmap k),
  #|T k A| >= 2.
Proof.
move => A.
case ET: #|T k A| => [|n]. by move: (Tneq0 A).
case En: n => [|m]. rewrite En in ET. by move: (Tneq1 A).
done.
Qed.

Lemma Teq2_enum {k} : forall (A : rtmap k), #|T k A| = 2 ->
  forall(z : T k A),
  let x := boundary k A ord0 in let y := e k A x in
  z = x \/ z = y.
Proof.
move => A ET z x y.
case: (altP (z =P x)) => [-> | /eqP /eqP Ezx]. by left.
right. case: (altP (z =P y)) => [-> | /eqP /eqP Ezy]. done.
have/eqP Eyx: y <> x by apply eall.
(* Isolate the set T \ {x} and prove its size is exactly 1 *)
have card_e1 : #|[predD1 T k A & x]| = 1.
  rewrite (cardD1 x) in ET. by apply/eq_add_S: ET.
(* Relax the equality to <= 1 so we can apply card_le1P *)
have card_le1 : #|[predD1 T k A & x]| <= 1 by rewrite card_e1.
(* Note that both z and y belong to this set T \ {x} *)
have zin : z \in [predD1 T k A & x] by rewrite inE Ezx.
have yin : y \in [predD1 T k A & x] by rewrite inE Eyx.
move/card_le1P: card_le1 => /(_ y yin) eq_pred1_y.
have := eq_pred1_y z. rewrite zin inE.
move => H. by have /eqP Ezyy: (z==y) by done. 
Qed.

Lemma Teq2_vyeqy {k} : forall (A : rtmap k), #|T k A| = 2 ->
  let x := boundary k A ord0 in let y := e k A x in v k A y = y.
Proof.
move => A ET x y. have /eqP Eyx: y <> x by apply eall.
case (Teq2_enum A ET (v k A y)) => Evy. 
move: (f_equal (square (v k A)) Evy) => Ev3y.
unfold square in Ev3y. rewrite v3 !vboundary in Ev3y.
by rewrite Ev3y eq_refl in Eyx. done.
Qed.
  
Lemma Teq2_kneq0 {k} : forall (A : rtmap k),
  #|T k A| = 2 -> k != 0.
Proof.
move => A ET. apply/eqP => Ek. move: A ET. rewrite Ek => A ET.
set x := boundary 0 A ord0. set y := e 0 A x.
have /eqP Eyx: y <> x by apply eall. move: (Teq2_vyeqy A ET) => Evy.
move: ((vtrivalent 0 A) y Evy) => [i Ei]. rewrite ord1 in Ei.
by rewrite Ei eq_refl in Eyx.
Qed.

Lemma Teq2_kleq2 {k} : forall (A : rtmap k),
  #|T k A| = 2 -> k < 2.
Proof.
move => A ET. rewrite ltnNge. apply/negP=> E1.
have: #|'I_(k.+1)| <= #|T k A|.
apply (leq_card (boundary k A)). by apply boundary_inj.
rewrite card_ord ET.
case Ek: k => [|l]. by rewrite Ek in E1.
case El: l => [|m]. by rewrite Ek El in E1.
done.
Qed.

Lemma Teq2_keq1 {k} : forall (A : rtmap k),
  #|T k A| = 2 -> k = 1.
Proof.
move => A ET.
case Ek: k => [|l]. move: (Teq2_kneq0 A ET) => E0. by rewrite Ek in E0.
case El: l => [|m]. done. move: (Teq2_kleq2 A ET) => E2. by rewrite Ek El in E2.
Qed.

Lemma Teq2_Atriv {k} (A : rtmap k) (ET : #|T k A| = 2) :
  isomorphic A rtVar.
Proof.
move: (Teq2_keq1 A ET) => Ek. move: A ET. rewrite Ek => A ET.
set y := boundary 1 A ord0. set z := e 1 A y.
have /eqP Ezy: z <> y by apply eall.
set phi : T 1 A -> T 1 rtVar := (fun x => if x==y then inl tt else inr tt).
apply inhabits. refine {|phi:=phi;keq:=erefl|}.
+
move => x. case (Teq2_enum A ET x) => Ex; rewrite Ex.
  - by rewrite vboundary.
  - by rewrite Teq2_vyeqy.
+
move => x. case (Teq2_enum A ET x) => Ex; rewrite Ex.
  - unfold phi. by rewrite (negPf Ezy) eq_refl.
  - unfold phi. by rewrite e2 eq_refl (negPf Ezy).
+
move => i. unfold phi. case (ord2_enum i) => Ei; rewrite Ei.
by rewrite eq_refl.
have Eb: (boundary 1 A ord2_1 == y = false). apply/negP => /eqP Eb.
  by move: (boundary_inj 1 A ord2_1 ord0 Eb).
by rewrite Eb.
Qed.

Lemma Tgt2_vyneqy {k} : forall (A : rtmap k), #|T k A| > 2 ->
  let x := boundary k A ord0 in let y := e k A x in v k A y != y.
Proof.
move => A ET. set x := boundary k A ord0. set y := e k A x.
apply/negP. move/eqP => Evy.
have /eqP Eyx: y <> x by apply eall.
have [z /andP [Ezx Ezy]] : exists z, (z != x) && (z != y).
{
rewrite (cardD1 x) in ET. simpl in ET.
have H2: 2 = 1 + 1 by done. rewrite H2 ltn_add2l in ET.
rewrite (cardD1 y) in ET. simpl in ET.
have Ey: (y \in [predD1 T k A & x]). rewrite inE.
apply/andP. by split. rewrite Ey in ET.
have H1: 1 = 1 + 0 by done. rewrite H1 ltn_add2l in ET.
Search (#|_| > _).
move/card_gt0P: ET => [z Ez]. rewrite !inE in Ez.
case/and3P: Ez => [Ezy Ezx _].
exists z. by apply/andP.
}
move: (trans k A z) => Exz. move: Ezx Ezy.
elim: Exz => [| w Hw | w Hw] //=.
by rewrite eq_refl.
case Ewx: (w == x); case Ewy: (w == y); move: Ewx Ewy => /eqP Ewx /eqP Ewy //=.
by rewrite Ewx vboundary eq_refl.
by rewrite Ewx vboundary eq_refl.
by rewrite Ewy Evy eq_refl.
move => H _ _. by apply H.
case Ewx: (w == x); case Ewy: (w == y); move: Ewx Ewy => /eqP Ewx /eqP Ewy //=.
by rewrite Ewx eq_refl.
by rewrite Ewx eq_refl.
have Eey: e k A y = x. unfold y. by rewrite e2.
by rewrite Ewy Eey eq_refl.
move => H _ _. by apply H.
Qed.

Lemma Tgt2_four {k} : forall (A : rtmap k), #|T k A| > 2 ->
  let  x := boundary k A ord0 in let y := e k A x   in
  let rA := v k A y           in let rB := v k A rA in
  (x != y /\ x != rA /\ x != rB) /\
            (y != rA /\ y != rB) /\
                      (rA != rB).
Proof.
move => A ET x y rA rB.
have /eqP Eyx: y <> x by apply eall.
move: (Tgt2_vyneqy A ET) => Evy. simpl in Evy. fold x y rA in Evy.
repeat split; apply/eqP => H.
+
by rewrite H eq_refl in Eyx.
+
move: (f_equal (square (v k A)) H) => Hv. unfold square in Hv.
rewrite v3 !vboundary in Hv. by rewrite -Hv eq_refl in Eyx.
+
move: (f_equal (v k A) H) => Hv.
rewrite v3 !vboundary in Hv. by rewrite -Hv eq_refl in Eyx.
+
by rewrite -H eq_refl in Evy.
+
move: (f_equal (v k A) H) => Hv. rewrite v3 in Hv.
by rewrite -Hv eq_refl in Evy.
+
move: (f_equal (square (v k A)) H) => Hv. unfold square in Hv.
rewrite v3 in Hv. by rewrite Hv eq_refl in Evy.
Qed.

Lemma Tgt2_preT {k} : forall (A : rtmap k), #|T k A| > 2 ->
  let  x := boundary k A ord0 in let y := e k A x   in
  let rA := v k A y           in let rB := v k A rA in
  let preT := [set z : T k A | (z != x)&&(z != y) ] in
  rA \in preT /\ rB \in preT.
Proof.
move => A ET x y rA rB preT. rewrite !inE.
move: (Tgt2_four A ET) => H. simpl in H. fold x y rA rB in H.
  move: H => [[Exy [Exa Exb]] [[Eya Eyb] Eab]].
split; apply/andP; split; by rewrite eq_sym.
Qed.

Lemma Tgt2_triv {k} (A : rtmap k) (ET : #|T k A| > 2) :
  let  x := boundary k A ord0 in let y := e k A x   in
  let rA := v k A y           in let rB := v k A rA in
  let preT := [set z : T k A | (z != x)&&(z != y) ] in
  forall z (B : {x | x \in preT}), z \in preT = false -> insubd B z = B.
Proof.
move => x y rA rB preT z B Ez. rewrite /insubd /odflt /oapp. case: insubP.
move => E H. by rewrite H in Ez. done.
Qed.

Lemma zIez {k} (A : rtmap k) :
  let  x := boundary k A ord0 in let y := e k A x   in
  let rA := v k A y           in let rB := v k A rA in
  let preT := [set z : T k A | (z != x)&&(z != y) ] in
  forall z, z \in preT -> e k A z \in preT.
Proof.
move => x y rA rB preT z Ez.  
apply/negP. rewrite inE.
move => /negP E. rewrite negb_and in E.
rewrite !negbK in E. move/orP: E => [/eqP H | /eqP H]; move: (f_equal (e k A) H);
rewrite !e2 => E; move: Ez; rewrite inE; rewrite !E eq_refl.
by move/andP => [H1 H2]. done.
Qed.

Inductive r_prop {T : finType} (z : T) (v e : T -> T) (root : T) : T -> Prop :=
| r_r : (r_prop z v e root) root
| r_v : forall x, z != x -> z != v x -> z != v (v x) ->
                      (r_prop z v e root) x -> (r_prop z v e root) (v x)
| r_e : forall x, (r_prop z v e root) x -> (r_prop z v e root) (e x).

Lemma r_prop_trans {T : finType} (b z : T) (v e : T -> T) (x y : T) :
  r_prop z v e x b -> r_prop z v e b y -> r_prop z v e x y.
Proof.
move => Exb Eby.
elim: Eby => [| w Ev0 Ev1 Ev2 _ IH | w _ IH] //=.
+ by apply r_v.
+ by apply r_e.
Qed.

Program Definition Tgt2_conn {k} (A : rtmap k) (ET : #|T k A| > 2)
  (EAB : r_prop (e k A (boundary k A ord0)) (v k A) (e k A) (v k A (e k A (boundary k A ord0))) (v k A (v k A (e k A (boundary k A ord0)))))
: rtmap (S k) :=
  let  x := boundary k A ord0 in let y := e k A x   in
  let rA := v k A y           in let rB := v k A rA in
  let preT := [set z : T k A | (z != x)&&(z != y) ] in
  let rAT := Sub rA _ : {x | x \in preT} in
  let rBT := Sub rB _ : {x | x \in preT} in
{|
T := {x | x \in preT};
v := fun d => if d == rAT then rAT else
              if d == rBT then rBT else
              insubd rAT (v k A (val d));
e := fun d => insubd rAT (e k A (val d));
boundary := fun i : 'I_(k.+2) =>
              if i == ord0 then rAT else
              match unlift ord_max i with
              | None    => rBT
              | Some j  => insubd rAT (boundary k A j)
              end;
|}.
Next Obligation. (* HA *)
move: (Tgt2_preT A ET) => H. simpl in H. by move: H => [HA HB].
Qed.
Next Obligation. (* HB *)
move: (Tgt2_preT A ET) => H. simpl in H. by move: H => [HA HB].
Qed.
Next Obligation. (* boundary_inj *)
set x := boundary k A ord0. set y := e k A x.
set rA := v k A y. set rB := v k A rA.
set preT := [set z : T k A | (z != x)&&(z != y) ].
set rAT := Sub rA _ : {x | x \in preT}.
set rBT := Sub rB _ : {x | x \in preT}.
move => s t. case: ifP => /eqP Es; case: ifP => /eqP Et. by rewrite Es.
+
case: (unliftP ord_max t) => j Ej.
Check insubdK.
Check val_insubd.
have H: (j <> ord0). move => H. rewrite H in Ej. unfold lift in Ej.
  unfold bump in Ej. simpl in Ej. rewrite Ej in Et. by case: Et; apply/val_inj.
have Hj: boundary k A j \in preT. rewrite inE. apply/andP. split;
  apply/negP => /eqP E. by apply boundary_inj in E.
  move: (Tgt2_vyneqy A ET). simpl. fold x y.
  by rewrite -E (vboundary k A j) eq_refl.
move => Er. move: (f_equal val Er). rewrite (insubdK _ Hj). simpl.
move: (Tgt2_four A ET) => HT. simpl in HT. fold x y rA rB in HT.
  move: HT => [[Exy [Exa Exb]] [[Eya Eyb] Eab]].
move => EAb. move: (f_equal (v k A) EAb). fold rB. rewrite vboundary.
move => EBb. rewrite -EBb in EAb. by rewrite EAb eq_refl in Eab.
+
move: (Tgt2_four A ET) => HT. simpl in HT. fold x y rA rB in HT.
  move: HT => [[Exy [Exa Exb]] [[Eya Eyb] Eab]].
move: (f_equal val Ej). simpl => H. by rewrite H eq_refl in Eab.
+
case: (unliftP ord_max s) => j Ej.
have H: (j <> ord0). move => H. rewrite H in Ej. unfold lift in Ej.
  unfold bump in Ej. simpl in Ej. rewrite Ej in Es. by case: Es; apply/val_inj.
have Hj: boundary k A j \in preT. rewrite inE. apply/andP. split;
  apply/negP => /eqP E. by apply boundary_inj in E.
  move: (Tgt2_vyneqy A ET). simpl. fold x y.
  by rewrite -E (vboundary k A j) eq_refl.
move => Er. move: (f_equal val Er).
rewrite (insubdK _ Hj). simpl.
move: (Tgt2_four A ET) => HT. simpl in HT. fold x y rA rB in HT.
  move: HT => [[Exy [Exa Exb]] [[Eya Eyb] Eab]].
move => EAb. move: (f_equal (v k A) EAb). fold rB. rewrite vboundary.
move => EBb. rewrite EBb in EAb. by rewrite EAb eq_refl in Eab.
+
move: (Tgt2_four A ET) => HT. simpl in HT. fold x y rA rB in HT.
  move: HT => [[Exy [Exa Exb]] [[Eya Eyb] Eab]].
move: (f_equal val Ej). simpl => H. by rewrite H eq_refl in Eab.
+
case: (unliftP ord_max s) => i Ei. case: (unliftP ord_max t) => j Ej.
have I: (i <> ord0). move => I. rewrite I in Ei. unfold lift in Ei.
  unfold bump in Ei. simpl in Ei. rewrite Ei in Es. by case: Es; apply/val_inj.
have Hi: boundary k A i \in preT. rewrite inE. apply/andP. split;
  apply/negP => /eqP E. by apply boundary_inj in E.
  move: (Tgt2_vyneqy A ET). simpl. fold x y.
  by rewrite -E (vboundary k A i) eq_refl.
have H: (j <> ord0). move => H. rewrite H in Ej. unfold lift in Ej.
  unfold bump in Ej. simpl in Ej. rewrite Ej in Et. by case: Et; apply/val_inj.
have Hj: boundary k A j \in preT. rewrite inE. apply/andP. split;
  apply/negP => /eqP E. by apply boundary_inj in E.
  move: (Tgt2_vyneqy A ET). simpl. fold x y.
  by rewrite -E (vboundary k A j) eq_refl.
move => Er. move: (f_equal val Er).
rewrite (insubdK _ Hi). rewrite (insubdK _ Hj).
move/boundary_inj => Eb. by rewrite Ei Ej Eb.
+
have I: (i <> ord0). move => I. rewrite I in Ei. unfold lift in Ei.
  unfold bump in Ei. simpl in Ei. rewrite Ei in Es. by case: Es; apply/val_inj.
have Hi: boundary k A i \in preT. rewrite inE. apply/andP. split;
  apply/negP => /eqP E. by apply boundary_inj in E.
  move: (Tgt2_vyneqy A ET). simpl. fold x y.
  by rewrite -E (vboundary k A i) eq_refl.
move: (f_equal val Ej). rewrite (insubdK _ Hi). simpl.
move: (Tgt2_four A ET) => HT. simpl in HT. fold x y rA rB in HT.
  move: HT => [[Exy [Exa Exb]] [[Eya Eyb] Eab]].
move => EAb. move: (f_equal (v k A) EAb). fold rB. rewrite vboundary.
move => EBb. rewrite EBb in EAb. by rewrite -EAb v3 eq_refl in Eyb.
+
move: Ei. case: (unliftP ord_max t). move => j Ej.
have H: (j <> ord0). move => H. rewrite H in Ej. unfold lift in Ej.
  unfold bump in Ej. simpl in Ej. rewrite Ej in Et. by case: Et; apply/val_inj.
have Hj: boundary k A j \in preT. rewrite inE. apply/andP. split;
  apply/negP => /eqP E. by apply boundary_inj in E.
  move: (Tgt2_vyneqy A ET). simpl. fold x y.
  by rewrite -E (vboundary k A j) eq_refl.
move => Er. move: (f_equal val Er).
rewrite (insubdK _ Hj). simpl.
move: (Tgt2_four A ET) => HT. simpl in HT. fold x y rA rB in HT.
  move: HT => [[Exy [Exa Exb]] [[Eya Eyb] Eab]].
move => EAb. move: (f_equal (v k A) EAb). fold rB. rewrite vboundary.
move => EBb. rewrite -EBb in EAb. by rewrite EAb v3 eq_refl in Eyb.
+
move => j. by rewrite i j.
Qed.
Next Obligation. (* vboundary *)
set x := boundary k A ord0. set y := e k A x.
set rA := v k A y. set rB := v k A rA.
set preT := [set z : T k A | (z != x)&&(z != y) ].
set rAT := Sub rA _ : {x | x \in preT}.
set rBT := Sub rB _ : {x | x \in preT}.
case: ifP; case: ifP; move/eqP => Ei. done.
case: (unliftP ord_max i).
  move => j Ej /eqP H. by rewrite H.
  move => Ej /eqP H. by rewrite H.
by rewrite eq_refl.
+
case: (unliftP ord_max i) => [j Ej | Ej] /eqP H.
case: ifP => /eqP EH. done.
have I: (j <> ord0). move => I. rewrite I in Ej. unfold lift in Ei.
  unfold bump in Ei. simpl in Ei. rewrite Ej in Ei. by case: Ei; apply/val_inj.
have Ev: (boundary k A j) \in preT. rewrite inE. apply/andP. split;
apply/negP => /eqP Eb. apply boundary_inj in Eb. by rewrite Eb in I.
move: (Tgt2_four A ET) => HT. simpl in HT. fold x y rA rB in HT.
  move: HT => [[Exy [Exa Exb]] [[Eya Eyb] Eab]].
move: (f_equal (v k A) Eb). fold rA. rewrite vboundary.
move => EBb. rewrite EBb in Eb. by rewrite Eb eq_refl in Eya.
+
by rewrite (insubdK _ Ev) vboundary.
+
by rewrite eq_refl.
Qed.
Next Obligation. (* vtrivalent *)
move: x H0 H.
set x := boundary k A ord0. set y := e k A x.
set rA := v k A y. set rB := v k A rA.
set preT := [set z : T k A | (z != x)&&(z != y) ].
set rAT := Sub rA _ : {x | x \in preT}.
set rBT := Sub rB _ : {x | x \in preT}.
move => z Ez Hz. case Es: (Sub z Ez == rAT) in Hz. by exists ord0.
case Et: (Sub z Ez == rBT) in Hz. exists ord_max. simpl. rewrite unlift_none.
by rewrite Hz.
+
move: (f_equal val Hz). simpl.
case Ev: ((v k A z) \in preT).
rewrite (insubdK _ Ev) => Hv. move: (vtrivalent k A z Hv) => [i Ei].
have Hi: i <> ord0. move => H. rewrite H in Ei. rewrite Ei inE in Ev.
  move/andP: Ev => [Ex Ey]. by rewrite vboundary eq_refl in Ex.
have Em: (ord_max : 'I_k.+2) <> (ord0 : 'I_k.+2) by done.
have Hli: lift ord_max i <> ord0. move => H. move: (f_equal val H).
  move: (lift_max i) => EH. assert (i = ord0). apply val_inj. simpl.
  by rewrite -EH H. by rewrite H0 in Hi.
exists (lift ord_max i). move/eqP: Hli => Hli. rewrite (negPf Hli).
by rewrite liftK -Ei -{2}Hv.
+
rewrite inE Bool.andb_false_iff in Ev. case: Ev => /eqP H.
move: (f_equal (square (v k A)) H). unfold square. rewrite v3 !vboundary.
fold x => E. have: z \in preT by done. rewrite inE => /andP [Ex Ey].
by rewrite E eq_refl in Ex.
move: (f_equal (square (v k A)) H). unfold square. rewrite v3. fold rA rB => EB.
exists ord_max. simpl. rewrite unlift_none. by apply val_inj.
Qed.
Next Obligation. (* v3 *)
move: x H.
set x := boundary k A ord0. set y := e k A x.
set rA := v k A y. set rB := v k A rA.
set preT := [set z : T k A | (z != x)&&(z != y) ].
set rAT := Sub rA _ : {x | x \in preT}.
set rBT := Sub rB _ : {x | x \in preT}.
move => z Ez.
move: (Tgt2_four A ET) => HT. simpl in HT. fold x y rA rB in HT.
  move: HT => [[Exy [Exa Exb]] [[Eya Eyb] Eab]].
case: ifP; case: ifP; case: ifP.
+
move/eqP => H. by rewrite H.
+
case: ifP. move => _ _ /eqP H. move: (f_equal val H) => E.
simpl in E. by rewrite E eq_refl in Eab.
+
case Ev: ((v k A z) \in preT). move => _ _ /eqP H _.
move: (f_equal val H). rewrite (insubdK _ Ev) => Hv. simpl in Hv.
move: (f_equal (square (v k A)) Hv). unfold square. rewrite !v3 => E.
have: z \in preT by done. rewrite inE => /andP [Ex Ey]. by rewrite E eq_refl in Ey.
rewrite inE Bool.andb_false_iff in Ev. case: Ev => /eqP H.
move: (f_equal (square (v k A)) H). unfold square. rewrite !v3 !vboundary => E.
have: z \in preT by done. rewrite inE => /andP [Ex Ey]. by rewrite E eq_refl in Ex.
move: (f_equal (square (v k A)) H). unfold square. rewrite !v3 => E. fold rA rB in E.
have /eqP EH: exist (fun x0 : T k A => x0 \in preT) z Ez = rBT by apply val_inj.
by rewrite EH.
+
move/eqP => H. by rewrite H.
+
case: ifP => H1 H2 H3. rewrite eq_refl => /eqP H.
  move: (f_equal val H) => E. simpl in E. by rewrite E eq_refl in Eab.
case: ifP => H4 /eqP H.
  move: (f_equal val H) => E. simpl in E. by rewrite E eq_refl in Eab.
rewrite -H. have Ev: (v k A z) \in preT. rewrite inE. apply/andP. split;
apply/negP => /eqP Ev. 
  have E: x \notin preT by rewrite inE eq_refl.
  have Ec: insubd rAT x = rAT. apply val_inj. rewrite /insubd /odflt /oapp.
    case: insubP. move/negP: E => E u H5. by rewrite H5 in E. done.
  by rewrite Ev Ec eq_refl in H3.
  have E: y \notin preT. rewrite inE eq_refl. apply/negP. by move => /andP [H5 E].
  have Ec: insubd rAT y = rAT. apply val_inj. rewrite /insubd /odflt /oapp.
    case: insubP. move/negP: E => E u H5. by rewrite H5 in E. done.
  by rewrite Ev Ec eq_refl in H3.
rewrite (insubdK _ Ev). rewrite (insubdK _ Ev) in H. rewrite H.
apply val_inj. simpl.
case Evv: ((v k A (v k A z)) \in preT).
-
move: (f_equal val H). rewrite (insubdK _ Evv). simpl => Ev2.
move: (f_equal (v k A) Ev2). rewrite v3. fold rB => Hv.
have Es: Sub z Ez = rBT by apply val_inj. by rewrite -Es eq_refl in H1.
-
rewrite inE Bool.andb_false_iff in Evv. case: Evv => /eqP Eb.
move: (f_equal (v k A) Eb). rewrite v3 vboundary => E.
have: z \in preT by done. rewrite inE => /andP [Ex Ey]. by rewrite E eq_refl in Ex.
move: (f_equal (square (v k A)) Eb). unfold square. rewrite !v3 => E. fold rA rB in E.
have EH: insubd rAT (v k A z) = rBT. apply val_inj. rewrite E.
  have Ei: rB \in preT. rewrite inE. apply/andP. split; apply/negP => /eqP Ei.
  by rewrite Ei eq_refl in Exb. by rewrite Ei eq_refl in Eyb.
  by rewrite (insubdK _ Ei). 
by rewrite EH eq_refl in H4.
+
by rewrite eq_refl.
+
by rewrite eq_refl.
+
by rewrite eq_refl.
+
case: ifP => /eqP Eb /eqP H1 /eqP H2. rewrite !eq_refl. by rewrite Eb.
have Hz: (v k A z) \in preT.
  apply/negP => /negP Ec. rewrite inE in Ec. rewrite negb_and in Ec.
  rewrite !negbK in Ec. move/orP: Ec => [/eqP Ex | /eqP Ey].
  have H: insubd rAT (v k A z) = rAT. apply val_inj. rewrite Ex.
    have E: x \notin preT by rewrite inE eq_refl.
    rewrite /insubd /odflt /oapp. case: insubP. move/negP: E => E u H.
    by rewrite H in E. done. by rewrite H in H2.
  have H: insubd rAT (v k A z) = rAT. apply val_inj. rewrite Ey.
    have E: y \notin preT. rewrite inE eq_refl. apply/negP. by move => /andP [H E].
    rewrite /insubd /odflt /oapp. case: insubP. move/negP: E => E u H.
    by rewrite H in E. done. by rewrite H in H2.
case: ifP => /eqP Ev H3. move: (f_equal val Ev). simpl => Evv.
rewrite (insubdK _ Hz) in Evv. move: (f_equal (square (v k A)) Evv).
unfold square. rewrite !v3 => Er.
have Ec: exist (fun x : T k A => x \in preT) z Ez = rAT by apply val_inj.
by rewrite Ec in H1.
rewrite (insubdK _ Hz). rewrite (insubdK _ Hz) in H3.
have Hzz: v k A (v k A z) \in preT.
  apply/negP => /negP Ec. rewrite inE in Ec. rewrite negb_and in Ec.
  rewrite !negbK in Ec. move/orP: Ec => [/eqP Ex | /eqP Ey].
  have H: insubd rAT (v k A (v k A z)) = rAT. apply val_inj. rewrite Ex.
    have E: x \notin preT by rewrite inE eq_refl.
    rewrite /insubd /odflt /oapp. case: insubP. move/negP: E => E u H.
    by rewrite H in E. done. by rewrite H eq_refl in H3.
  have H: insubd rAT (v k A (v k A z)) = rAT. apply val_inj. rewrite Ey.
    have E: y \notin preT. rewrite inE eq_refl. apply/negP. by move => /andP [H E].
    rewrite /insubd /odflt /oapp. case: insubP. move/negP: E => E u H.
    by rewrite H in E. done. by rewrite H eq_refl in H3.
case: ifP => /eqP Evv. move: (f_equal val Evv). simpl => Ev3.
rewrite (insubdK _ Hzz) in Ev3. move: (f_equal (v k A) Ev3).
unfold square. rewrite !v3 => Er.
have: z \in preT by done. rewrite inE => /andP [Ex Ey]. by rewrite Er eq_refl in Ey.
apply val_inj. simpl. by rewrite (insubdK _ Hzz) v3 (insubdK _ Ez).
Qed.
Next Obligation. (* eall *)
move: x H.
set x := boundary k A ord0. set y := e k A x.
set rA := v k A y. set rB := v k A rA.
set preT := [set z : T k A | (z != x)&&(z != y) ].
set rAT := Sub rA _ : {x | x \in preT}.
move: (Tgt2_preT A ET). simpl. fold x y rA rB preT => H. move: H => [Ea Eb].
set rBT := Sub rB Eb : {x | x \in preT}.
move => z Ez.
have EH: e k A z \in preT. apply/negP. rewrite inE.
  move => /negP E. rewrite negb_and in E.
  rewrite !negbK in E. move/orP: E => [/eqP H | /eqP H]; move: (f_equal (e k A) H);
  rewrite !e2 => E; move: Ez; rewrite inE; rewrite !E eq_refl.
  by move/andP => [H1 H2]. done.
move => H. move: (f_equal val H). rewrite (insubdK _ EH). simpl. by apply eall.
Qed.
Next Obligation. (* e2 *)
move: x H.
set x := boundary k A ord0. set y := e k A x.
set rA := v k A y. set rB := v k A rA.
set preT := [set z : T k A | (z != x)&&(z != y) ].
set rAT := Sub rA _ : {x | x \in preT}.
move: (Tgt2_preT A ET). simpl. fold x y rA rB preT => H. move: H => [Ea Eb].
set rBT := Sub rB Eb : {x | x \in preT}.
move => z Ez.
apply val_inj. by rewrite (insubdK _ (zIez A z Ez)) e2 (insubdK _ Ez).
Qed.
Next Obligation. (* trans *)
set x := boundary k A ord0. set y := e k A x.
set rA := v k A y. set rB := v k A rA.
set preT := [set z : T k A | (z != x)&&(z != y) ].
set rAT := Sub rA _ : {x | x \in preT}.
set rBT := Sub rB _ : {x | x \in preT}.
set f_v := (fun d : {x0 : T k A | x0 \in preT} =>
   if d == rAT then rAT else if d == rBT then rBT else insubd rAT (v k A (sval d))).
set f_e := (fun d : {x0 : T k A | x0 \in preT} => insubd rAT (e k A (sval d))).
have fe2: forall x, f_e (f_e x) = x.
move => [z Ez].
have EH: e k A z \in preT. apply/negP. rewrite inE.
  move => /negP E. rewrite negb_and in E.
  rewrite !negbK in E. move/orP: E => [/eqP H | /eqP H]; move: (f_equal (e k A) H);
  rewrite !e2 => E; move: Ez; rewrite inE; rewrite !E eq_refl.
  by move/andP => [H1 H2]. done.
apply val_inj. unfold f_e. by rewrite (insubdK _ EH) e2 (insubdK _ Ez).

move => [z Ez]. fold x y rA rB in EAB. move: (trans k A z) => Rz.
apply (reachsym (v k A) (e k A) (v3 k A) (e2 k A)) in Rz.
apply reach_e in Rz. apply reach_v in Rz. fold x y rA in Rz.
apply (reachsym (v k A) (e k A) (v3 k A) (e2 k A)) in Rz.
induction Rz as [| u Eu IH | u Eu IH].
+
have H: exist (fun x0 : T k A => x0 \in preT) rA Ez = rAT by apply val_inj.
rewrite H. apply reach_r.
+
case H: (u \in preT).
-
have E: u != rA ->
exist (fun x0 : T k A => x0 \in preT) (v k A u) Ez = f_v (insubd rAT u).
  move => Hu. apply val_inj. unfold f_v. simpl.
  have /eqP EH: insubd rAT u <> rAT. move => E. move: (f_equal sval E).
    rewrite (insubdK _ H) => F. by rewrite F eq_refl in Hu.
  rewrite (negPf EH).
  case Eb: (insubd rAT u == rBT); move/eqP: Eb => Eb. move: (f_equal val Eb).
    rewrite (insubdK _ H). simpl => Er. have: v k A u \in preT by done.
    rewrite inE Er. by rewrite v3 eq_refl => /andP [H1 H2].
  rewrite (insubdK _ H). by rewrite (insubdK _ Ez).
case Hu: (u == rA). move/eqP: Hu => Hu.
have Ev: (exist (fun x0 : T k A => x0 \in preT) (v k A u) Ez) = rBT. apply val_inj.
  simpl. by rewrite Hu. rewrite Ev.
(* THE HARD PART *)
move: (Tgt2_preT A ET). simpl. fold x y rA rB preT => EH. move: EH => [Ea Eb].
have Era: rAT = insubd rAT rA. apply val_inj. by rewrite (insubdK _ Ea).
have Erb: rBT = insubd rAT rB. apply val_inj. by rewrite (insubdK _ Eb).
rewrite Era Erb. clear u Ez Eu IH H E Hu Ev.
elim: EAB. apply reach_r.
move => z Ev0 Ev1 Ev2 _ IH.
case Eza: (z == rA); move/eqP: Eza => Eza. rewrite Eza -Erb.
by rewrite Eza v3 eq_refl in Ev2.
have Er: insubd rAT (v k A z) = f_v (insubd rAT z). unfold f_v.
case Ez: (z \in preT).
have Ee: insubd rAT z != rAT. apply/negP => /eqP H. move: (f_equal sval H).
rewrite (insubdK _ Ez). simpl => EH. by rewrite EH in Eza.
rewrite (negPf Ee).
case: ifP; move => /eqP Ezb.
move: (f_equal sval Ezb). rewrite (insubdK _ Ez). simpl => Ec.
by rewrite Ec v3 eq_refl in Ev1.
by rewrite (insubdK _ Ez).
move: (Tgt2_triv A ET z rAT Ez) => Er. rewrite Er eq_refl.
rewrite inE Bool.andb_false_iff in Ez. case: Ez => /eqP Ez.
rewrite Ez vboundary.
have Ex: (x \in preT = false) by rewrite inE eq_refl.
move: (Tgt2_triv A ET x rAT Ex) => Exx. by rewrite Exx.
by rewrite Ez -Era.
rewrite Er. by apply reach_v.

move => z _ IH.
case Ez: (z \in preT).
have Ee: insubd rAT (e k A z) = f_e (insubd rAT z). unfold f_e.
  by rewrite (insubdK _ Ez).
rewrite Ee. by apply reach_e.
rewrite inE Bool.andb_false_iff in Ez. case: Ez => /eqP Ez.
have Ey: (y \in preT = false) by rewrite inE eq_refl Bool.andb_false_r.
rewrite Ez. move: (Tgt2_triv A ET y rAT Ey) => Er. rewrite Er -Era. apply reach_r.
rewrite Ez e2.
have Ex: (x \in preT = false) by rewrite inE eq_refl.
move: (Tgt2_triv A ET x rAT Ex) => Er. rewrite Er -Era. apply reach_r.
(* END OF HARD PART *)

move/eqP: Hu => /eqP Hu. rewrite (E Hu). apply reach_v.
have EH: insubd rAT u = (exist (fun x : T k A => x \in preT) u H). apply val_inj.
  by rewrite (insubdK _ H).
rewrite EH. move/eqP: Hu => /eqP Hu. apply IH.
-
rewrite inE Bool.andb_false_iff in H. case: H => /eqP H.
have: v k A u \in preT by done. rewrite inE => /andP [H1 H2].
by rewrite H vboundary eq_refl in H1.
have E: exist (fun x0 : T k A => x0 \in preT) (v k A u) Ez = rAT. apply val_inj.
  simpl. by rewrite H.
rewrite E. apply reach_r.
+
case H: (u \in preT).
-
have E: exist (fun x0 : T k A => x0 \in preT) (e k A u) Ez = f_e (insubd rAT u).
  apply val_inj. unfold f_e. simpl. by rewrite (insubdK _ H) (insubdK _ Ez).
rewrite E. apply reach_e.
have EH: insubd rAT u = (exist (fun x : T k A => x \in preT) u H). apply val_inj.
  by rewrite (insubdK _ H).
rewrite EH. by apply IH.
-
rewrite inE Bool.andb_false_iff in H. case: H => /eqP H;
have: e k A u \in preT by done.
rewrite inE => /andP [Ex Ey]. by rewrite H eq_refl in Ey.
rewrite inE => /andP [Ex Ey]. rewrite H in Ex. unfold y in Ex.
  by rewrite e2 eq_refl in Ex.
Qed.





Definition step_avoid {k A} (z x y : T k A) : bool :=
  ((y == v k A x) && (y != z) && (v k A y != z) && (x != z)) || (y == e k A x).

Definition r_bool {k A} (z x y : T k A) : bool :=
  connect (step_avoid z) x y.

(* Refl *)
Check connect0.
Lemma r_bool_refl {k A z} (x : T k A) : r_bool z x x.
Proof. unfold r_bool. by rewrite connect0. Qed.

(* Trans *)
Lemma r_bool_trans {k A z w y} (x : T k A) :
r_bool z w x -> r_bool z x y -> r_bool z w y.
Proof. move => Ewx Exy. by apply (connect_trans Ewx). Qed.

Lemma r_bool_sym {k A x y} (z : T k A) :
r_bool z y x -> r_bool z x y.
Proof.
move/connectP => [p Hpath Hlast].
elim: p y Hpath Hlast => [| u p IH] current_node Hpath Hlast.
rewrite Hlast. apply connect0.
simpl in Hpath. move/andP: Hpath => [Hstep Hpath].
simpl in Hlast. move: (IH u Hpath Hlast) => EH.
apply (r_bool_trans u EH).
unfold step_avoid in Hstep. move/orP: Hstep => Hstep.
case: Hstep => H.
+
move/andP: H => [H H1]. move/andP: H => [H H2]. move/andP: H => [/eqP H3 H4].
move: (f_equal (square (v k A)) H3). 
  unfold square. rewrite v3 => H5. rewrite -H5 in H1. 
apply (r_bool_trans (v k A u)); apply connect1; unfold step_avoid; apply/orP
;left. by rewrite eq_refl H2 H1 H4. by rewrite -H5 eq_refl H1 v3 H4 H2.
+
apply connect1. unfold step_avoid. apply/orP. right. move/eqP: H => H.
by rewrite H e2.
Qed.

Lemma r_bool_e {k A z x y} : r_bool z x y -> r_bool z x (e k A y).
Proof.
move => Er. apply (r_bool_trans y). done.
apply connect1. apply/orP. by right.
Qed.

Lemma r_bool_v {k A z x y} : r_bool z x y -> y != z -> v k A y != z ->
v k A (v k A y) != z -> r_bool z x (v k A y).
Proof.
move => Er Ev1 Ev2 Ev0. apply (r_bool_trans y). done.
apply connect1. apply/orP. left. by rewrite eq_refl Ev1 Ev2 Ev0.
Qed.

Lemma neqsym {k A} (x y : T k A) : x != y -> y != x.
Proof. move => H. apply/negP => /eqP E. by rewrite E eq_refl in H. Qed.

Lemma bool_prop {k A} (z x y: T k A) :
  r_bool z x y -> r_prop z (v k A) (e k A) x y.
Proof.
move => Er.
move/connectP: Er => [p Hpath Hlast].
move: y Hlast Hpath. elim/last_ind: p => [|p w IH] y Hlast Hpath.
rewrite Hlast. apply r_r.
rewrite last_rcons in Hlast. rewrite rcons_path in Hpath.
move/andP: Hpath => [Hpath Hstep]. move: (IH (last x p) erefl Hpath) => EH.
unfold step_avoid in Hstep. move/orP: Hstep. case => [H | /eqP Ee].
move/andP: H => [H H1]. move/andP: H => [H H2]. move/andP: H => [/eqP H3 H4].
rewrite Hlast H3. apply r_v. by apply neqsym. rewrite -H3; by apply neqsym.
rewrite -H3; by apply neqsym. done.
rewrite Hlast Ee. by apply r_e.
Qed.

Lemma prop_bool {k A} (z x y: T k A) :
  r_prop z (v k A) (e k A) x y -> r_bool z x y.
Proof.
elim => [| w Ev0 Ev1 Ev2 _ IH | w _ IH].
apply r_bool_refl.
apply (r_bool_trans w). done.
  apply connect1. apply/orP. left.
  by rewrite eq_refl (neqsym _ _ Ev1) (neqsym _ _ Ev2) (neqsym _ _ Ev0).
apply (r_bool_trans w). done.
  apply connect1. apply/orP. by right.
Qed.

Lemma r_prop_bool {k A} (z x y: T k A) :
  reflect (r_prop z (v k A) (e k A) x y) (r_bool z x y).
Proof.
case Er: (r_bool z x y).
apply: ReflectT. by apply bool_prop.
apply: ReflectF => H. move: (prop_bool z x y H) => E. by rewrite E in Er.
Qed.





Lemma rtmap_decompose {k : nat} : forall (A : rtmap k),
(isomorphic A rtVar)          \/
(exists p q (P : rtmap p) (Q : rtmap q), 
  isomorphic A (rtApp P Q))   \/
(exists l (a : 'I_l.+1) (P : rtmap l.+1), 
  isomorphic A (rtAbs a P)).
Proof.
move => A. move: (Tgeq2 A) => Et. case T2: (#|T k A| == 2); move/eqP: T2 => T2.
left. by apply Teq2_Atriv. right.
have ET: 2 < #|T k A|. case #|T k A| as [|n]. done. case n as [|m]. done.
  by case m as [|l]. clear Et T2.
set x := boundary k A ord0. set y := e k A x.
set rA := v k A y. set rB := v k A rA.
set preT := [set z : T k A | (z != x)&&(z != y)].
move: (Tgt2_preT A ET). simpl. fold x y rA rB preT => H. move: H => [Ea Eb].
set rAT := Sub rA Ea : {x | x \in preT}. set rBT := Sub rB Eb : {x | x \in preT}.
have Era: rAT = insubd rAT rA. apply val_inj. by rewrite (insubdK _ Ea).
have Erb: rBT = insubd rAT rB. apply val_inj. by rewrite (insubdK _ Eb).
(* Non-trivial cases *)
case EAB: (r_bool y rA rB). move/r_prop_bool: EAB => EAB.
+ (* Abstraction case *)
right. exists k. exists ord_max. exists (Tgt2_conn A ET EAB).
apply inhabits.
set phi : T k A -> T k (rtAbs ord_max (Tgt2_conn A ET EAB)) := fun z =>
  if z == x then inl tt else if z == y then inr (inl tt) else
  inr (inr (insubd rAT z)).
have Er: rAT = Sub rA (Tgt2_conn_obligation_1 k A ET) by apply val_inj.
refine {|phi:=phi;keq:=erefl|}; unfold phi.
- move => z.
case Ex: (z == x); move/eqP: Ex => Ex.
by rewrite Ex vboundary eq_refl.
have Evx: v k A z != x. apply/negP => /eqP H. move: (f_equal (square (v k A)) H).
  unfold square. rewrite v3 !vboundary => E. by rewrite E in Ex.
rewrite (negPf Evx).
case Ey: (z == y); move/eqP: Ey => Ey.
rewrite Ey (negPf (Tgt2_vyneqy A ET)). unfold v. simpl. rewrite -Era.
by rewrite Er.
case Evy: (v k A z == y). move/eqP: Evy => Evy.
move: (f_equal (square (v k A)) Evy). unfold square. rewrite v3. fold rA rB => Eza.
unfold v. rewrite Eza. simpl.
have Ena: (insubd rAT rB == Sub (v k A (e k A (boundary k A ord0))) _) = false.
  move => i. apply/negP => /eqP H. move: (f_equal sval H). rewrite -Erb. simpl.
  move: (Tgt2_four A ET). simpl. fold x y rA rB => HT E.
  move: HT => [[Exy [Exa Exb]] [[Eya Eyb] Eab]]. by rewrite E eq_refl in Eab.
have Em: lift ord0 ord_max = ord_max. move => n. by apply val_inj.
have Eyb: (insubd rAT rB = Sub (v k A (v k A (e k A (boundary k A ord0)))) _).
  move => i. apply val_inj. by rewrite -Erb.
by rewrite Ena Em unlift_none -Eyb eq_refl.

move: Ex Ey => /eqP Ex /eqP Ey.
have Ez: z \in preT by rewrite inE Ex Ey.
case Eza: (z == rA). move/eqP: Eza => Eza.
have Et: insubd rAT z = Sub (v k A (e k A (boundary k A ord0))) _.
  move => i. apply val_inj. by rewrite (insubdK _ Ez).
have Em: lift ord0 ord_max = ord_max. move => n. by apply val_inj.
rewrite Eza. fold rB. unfold v. simpl.
have Ed: (insubd rAT rB) = (Sub (v k A (v k A (e k A
  (boundary k A ord0)))) (Tgt2_conn_obligation_2 k A ET)).
  apply val_inj. by rewrite (insubdK _ Eb).
by rewrite -Et Em unlift_none Eza eq_refl Ed.

have Evz: v k A z \in preT. rewrite inE. by rewrite Evx Evy.
have Ed: insubd rAT (v k A z) = insubd (Sub rA (Tgt2_conn_obligation_1 k A ET))
  (v k A z) by rewrite Er. rewrite Ed.
have Ena: (insubd rAT z == Sub rA (Tgt2_conn_obligation_1 k A ET)) = false.
  apply/negP => /eqP H. move: (f_equal sval H). rewrite (insubdK _ Ez).
  simpl => E. by rewrite E eq_refl in Eza.
have Em: lift ord0 ord_max = ord_max. move => n. by apply val_inj.
have Ezb: (insubd rAT z == Sub rB (Tgt2_conn_obligation_2 k A ET)) = false.
  apply/negP. move => /eqP H. move: (f_equal sval H). rewrite (insubdK _ Ez).
  simpl => E. move: (f_equal (v k A) E) => EH. by rewrite EH v3 eq_refl in Evy.
unfold v. simpl. fold x y rA rB. by rewrite Ena Em unlift_none Ezb (insubdK _ Ez).

- move => z.
move: (eall k A x) => /eqP Exy.
case Ex: (e k A z == x). move/eqP: Ex => Ex.
move: (f_equal (e k A) Ex). rewrite e2 => Exx. by rewrite Exx (negPf Exy) eq_refl.
case Ey: (e k A z == y). move/eqP: Ey => Ey.
move: (f_equal (e k A) Ey). rewrite e2 => Eyy. by rewrite Eyy e2 eq_refl.
have Exx: z != x. apply/negP => /eqP H. by rewrite H eq_refl in Ey.
have Eyy: z != y. apply/negP => /eqP H. by rewrite H e2 eq_refl in Ex.
have Ez: z \in preT by rewrite inE Exx Eyy.
unfold e. simpl. rewrite (negPf Exx) (negPf Eyy) (insubdK _ Ez).
have Ed: (insubd rAT ((let (T0, v0, e0, boundary0, _, _, _, _, _, _, _) as r
  return (T k r -> T k r) := A in e0) z)) = (insubd (Sub (v k A (e k A
  (boundary k A ord0))) (Tgt2_conn_obligation_1 k A ET)) (e k A z)).
apply val_inj. simpl. by rewrite !(insubdK _ (zIez A z Ez)).
by rewrite Ed.
- move => i.
case E0: (i == ord0). move/eqP: E0 => E0. by rewrite E0 eq_refl.
have Hx: boundary k A i != x. apply/negP => /eqP H. apply boundary_inj in H.
  by rewrite H eq_refl in E0.
rewrite (negPf Hx).
have Hy: boundary k A i != y. apply/negP => /eqP H. move: (vboundary k A i) => E.
  move: (Tgt2_vyneqy A ET). simpl. fold x y. by rewrite -H E eq_refl.
rewrite (negPf Hy).
have Em: lift ord0 ord_max = ord_max. move => n. by apply val_inj.
have En: nat_of_ord (lift ord_max i) != nat_of_ord ord0. move => n.
  apply/negP => /eqP H. rewrite lift_max in H.
  have E: i = ord0 by apply val_inj. by rewrite E eq_refl in E0.
have El: (lift ord_max i == ord0) = false. apply/negP => /eqP H. move: (En 0).
  by rewrite H eq_refl.
simpl. by rewrite cast_ord_id E0 Em El liftK Er.
+ (* Application case *)
left.
Admitted.





Section Partitioning.
Variable (k : nat).
Variable (A : rtmap k).

Let x := boundary k A ord0.
Let y := e k A x.
Let rA := v k A y.
Let rB := v k A rA.
Let preT := [set z : T k A | (z != x)&&(z != y) ].

Definition setA := [set z : T k A | r_bool y rA z ].
Definition setB := [set z : T k A | r_bool y rB z ].

Lemma partition (z : T k A) : (z == x) || (z == y) || (z \in setA) || (z \in setB).
Proof.
apply: contraT. rewrite !negb_or.
move => /andP [/andP [/andP [Ex Ey] EA] EB].
move: (trans k A z) => Er. induction Er. by rewrite eq_refl in Ex.
+
have Ea: v k A x0 != rA. apply/negP => /eqP H. by rewrite H inE r_bool_refl in EA.
have Eb: v k A x0 != rB. apply/negP => /eqP H. by rewrite H inE r_bool_refl in EB.
apply IHEr.
apply/negP => /eqP H. by rewrite H vboundary eq_refl in Ex.
apply/negP => /eqP H. by rewrite H eq_refl in Ea.
rewrite inE. apply/negP => H. rewrite inE in EA. rewrite (r_bool_v H) in EA.
  done. apply/negP => /eqP E. by rewrite E eq_refl in Ea.
  done. apply/negP => /eqP E. unfold rB in Eb. unfold rA in Eb.
  by rewrite -E v3 eq_refl in Eb.
rewrite inE. apply/negP => H. rewrite inE in EB. rewrite (r_bool_v H) in EB.
  done. apply/negP => /eqP E. by rewrite E eq_refl in Ea.
  done. apply/negP => /eqP E. unfold rB in Eb. unfold rA in Eb.
  by rewrite -E v3 eq_refl in Eb.
+
apply IHEr.
apply/negP => /eqP H. by rewrite H eq_refl in Ey.
apply/negP => /eqP H. by rewrite H e2 eq_refl in Ex.
rewrite inE. apply/negP => H. rewrite inE in EA. by rewrite (r_bool_e H) in EA.
rewrite inE. apply/negP => H. rewrite inE in EB. by rewrite (r_bool_e H) in EB.
Qed.

Lemma partition_disjoint : (r_bool y rA rB = false) -> [disjoint setA & setB].
Proof.
move => E. apply/pred0P => z. apply/negP => /andP [EA EB].
rewrite !inE in EA EB. by rewrite (r_bool_trans z EA (r_bool_sym y EB)) in E.
Qed.

Lemma partition_complete : setA :|: setB :|: [set x; y] = [set: T k A].
Proof.
apply/setP => z. rewrite !inE. move: (partition z). repeat case/orP.
move => ->. apply/orP. by right.
move => ->. apply/orP. right. apply/orP. by right.
rewrite inE. move => ->. apply/orP. left. apply/orP. by left.
rewrite inE. move => ->. apply/orP. left. apply/orP. by right.
Qed.  

Definition setAb := [set i : 'I_(S k) | (i != ord0) && r_bool y rA (boundary k A i) ].
Definition setBb := [set i : 'I_(S k) | (i != ord0) && r_bool y rB (boundary k A i) ].

Lemma partition_boundary (i: 'I_(S k)) (ET : #|T k A| > 2) :
  (i == ord0) || (i \in setAb) || (i \in setBb).
Proof.
apply: contraT. rewrite !negb_or. move => /andP [/andP [E0 EA] EB].
have Ex: (boundary k A i != x). apply/negP => /eqP H. apply boundary_inj in H.
  by rewrite H eq_refl in E0.
have Ey: (boundary k A i != y). apply/negP => /eqP H. move: (f_equal (v k A) H).
  rewrite vboundary H => E. move: (Tgt2_vyneqy A ET). simpl. fold x y.
  by rewrite -E eq_refl.
have Ea: (boundary k A i \notin setA). rewrite inE. apply/negP => H.
  by rewrite inE E0 H in EA.
have Eb: (boundary k A i \notin setB). rewrite inE. apply/negP => H.
  by rewrite inE E0 H in EB.
move: (partition (boundary k A i)). repeat case/orP.
move/eqP => H. by rewrite H eq_refl in Ex.
move/eqP => H. by rewrite H eq_refl in Ey.
rewrite inE => H. by rewrite inE H in Ea.
rewrite inE => H. by rewrite inE H in Eb.
Qed.

Lemma partition_boundary_disjoint: (r_bool y rA rB = false) ->
  [disjoint setAb & setBb].
Proof.
move => E. apply/pred0P => z. apply/negP => /andP [EA EB].
rewrite !inE in EA EB. move: EA EB => /andP [_ EA] /andP [_ EB].
by rewrite (r_bool_trans (boundary k A z) EA (r_bool_sym y EB)) in E.
Qed.
End Partitioning.

