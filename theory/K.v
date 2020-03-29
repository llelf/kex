From mathcomp   Require Import ssreflect ssrnat ssrbool ssrfun eqtype seq.
From QuickChick Require Import QuickChick.
From compcert   Require Import Integers IEEE754_extra.
From Hammer     Require Import Hammer Reconstr.
From Coq        Require Import Program ZArith.

Set Implicit Arguments.            Unset Strict Implicit.
Unset Printing Implicit Defensive. Set Bullet Behavior "None".

Module opt.
Fixpoint lift X Y Z (f:X->Y->Z) a b : option Z :=
  match a,b with | Some a,Some b => Some(f a b)
                 | _,_ => None
  end.

Definition sequenceA X (a:seq(option X)) : option(seq X) :=
  foldr (lift cons) (Some[::]) a.

Definition map := option_map.
End opt.


Module   I32:=Int.     Module   I64:=Int64.
Notation i32:=I32.int. Notation i64:=I64.int.
Notation "[i32 i m ]" := (I32.mkint i m).
Notation "[i64 i m ]" := (I64.mkint i m).



Inductive Nu := I of i32 | J of i64.
Inductive At := ANu of Nu.
Inductive Ty := Ti|Tj|TL.
Inductive K :=
| A of At
| L of Ty & nat & K & seq K.

Section arith.
Definition ONi := I(I32.repr I32.min_signed).
Definition ONj := J(I64.repr I64.min_signed).
Definition Oi := I I32.zero.
Definition Oj := J I64.zero.
Definition K0j := A(ANu Oj).  Definition K1j := A(ANu(J I64.one)).
Definition K0i := A(ANu Oi).  Definition K1i := A(ANu(I I32.one)).

Definition Kiofnat (n:nat):K := A(ANu(I(I32.repr(Z.of_nat n)))).
Definition Kjofnat (n:nat):K := A(ANu(J(I64.repr(Z.of_nat n)))).

Definition iwiden (a:i32):i64 := I64.repr(I32.signed a).

Definition addnu a b := match a,b with
  | I i, I j => I(I32.add i j)
  | J i, J j => J(I64.add i j)
  | I i, J j => J(I64.add (iwiden i)j)
  | J i, I j => J(I64.add i(iwiden j)) end.

Definition K2j := Kjofnat 2.

Definition eqnu a b := match a,b with
  | I i, I j => I32.eq i j
  | J i, J j => I64.eq i j
  | I i, J j => I64.eq (iwiden i)j
  | J i, I j => I64.eq i(iwiden j)
end.

Lemma wide_range a: (I64.min_signed<=I32.signed a<=I64.max_signed)%Z.
Admitted.

Lemma addnuC a b : addnu a b = addnu b a.
Proof.
elim a=>i; elim b=>j => /=.
- by rewrite I32.add_commut.
- rewrite/iwiden !I64.add_signed I64.signed_repr;
    [rewrite Z.add_comm//| exact: wide_range].
- rewrite/iwiden !I64.add_signed I64.signed_repr;
    [rewrite Z.add_comm//| exact: wide_range].
by rewrite I64.add_commut.
Qed.

Lemma addnu0i a : addnu a Oi = a.
Proof.
elim a=>i /=. by rewrite I32.add_zero.
by rewrite/iwiden I32.signed_zero I64.add_zero.
Qed.

Lemma addnu0j a : eqnu (addnu a Oj) a.
Proof.
elim a=>i /=.
- by rewrite/iwiden I64.add_zero I64.eq_true.
by rewrite I64.add_zero I64.eq_true.
Qed.
End arith.


Section ops.

Definition ktype (a:K):Ty := match a with
| A(ANu(I _))=>Ti | A(ANu(J _))=>Tj | L _ _ _ _=> TL
end.


Definition ksize (a:K):K := match a with
| A a => K1i | L _ n _ _ => Kiofnat n
end.

Notation "#:" := (ksize)(at level 10).



Fixpoint nullify (a:K):K := match a with
| A(ANu(I _))=> A(ANu Oi)
| A(ANu(J _))=> A(ANu Oj)
| L t n a aa => L t n (nullify a) (map nullify aa)
end.


(* Definition unil:K := L TL 0 _ [::]. *)

Definition khead (k:K):K := match k with
| A _=> k | L t 0 a _=> nullify a | L t n a _=> a
end.

Notation "*:" := (khead)(at level 10).

Definition krev (k:K):K := match k with
| A _=> k | L t 0 a _=> k
| L t n a bb=> let r:=rcons(rev bb)a in L t n (last a bb) (behead r)
end.

Notation "|:" := (krev)(at level 10).



Remark wtf_last T (a:T)(aa:seq T) :
  last (last a aa) (behead (rcons (rev aa) a)) = a.
Proof.
rewrite -(revK aa); set r:=rev aa; rewrite revK.
by case: r=> //= r rr; rewrite rev_cons last_rcons.
Qed.

Remark wtf_behead T (a:T)(aa:seq T) :
  behead (rcons (rev (behead (rcons (rev aa) a))) (last a aa)) = aa.
Proof.
rewrite -(revK aa); set r:=rev aa; rewrite revK.
case: r=> //= r rr. by rewrite rev_cons last_rcons rev_rcons rcons_cons.
Qed.



Lemma krevK : involutive (|:).
Proof.
case=> t // n a aa. case: n=> //= n. by rewrite wtf_last wtf_behead.
Qed.

Lemma size_krev a : #:(|:a) = #:a.
Proof. case: a=> // t n a aa. case: n=> //. Qed.


Definition enlist (a:K):K := L TL 1 a [::].

Notation ",:" := (enlist)(at level 10).

Lemma size_enlist a : #:(,:a) = K1i.  Proof. by[]. Qed.



Definition krconst (a b:K):K := b.
Notation "::" := (krconst)(at level 10).


Definition izero := I32.eq I32.zero.
Definition ipos := I32.lt I32.zero.
Definition ineg := I32.lt^~I32.zero.

Definition isI a := if a is A(ANu(I _)) then true else false.
Definition isIpos a := if a is A(ANu(I n)) then ipos n else false.


Definition kiota (a:K):option K := match a with
  | A(ANu(I ni))=>
    if izero ni then
      Some(L Ti 0 K0i nil)
    else if ipos ni then
      let n:=Z.to_nat (I32.signed ni)
      in Some(L Ti n K0i [seq Kiofnat i|i<-iota 1 n.-1])
    else None
  | _=> None
end.


Notation "!:" := (kiota)(at level 10).




Lemma i_dec (a:i32) : {a=I32.zero}
                     +{izero a=false /\ ipos a /\ ineg a=false}
                     +{izero a=false /\ ipos a=false /\ ineg a}.
Admitted.


Lemma size_kiota a : isIpos a -> option_map (#:)(!:a) = Some a.
Proof.
case: a=> //= a. case: a => // n. case: n=> //i POS.
case: (i_dec i). case.
- scrush.
- case=> ->[] -> _ /=. rewrite/Kiofnat Z2Nat.id.
  + by rewrite Int.repr_signed.
  move:POS. rewrite/ipos.
  ryreconstr (@Z.lt_le_incl, @I32.signed_zero) (@is_true, @I32.lt).
scrush.
Qed.


(* Definition kfold (a f:K):K := match a with *)
(*   | A a=> a | L _ _ a aa=> foldl  *)


End ops.
