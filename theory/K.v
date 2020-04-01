From mathcomp   Require Import ssreflect ssrnat ssrbool ssrfun eqtype seq.
From QuickChick Require Import QuickChick.
From compcert   Require Import Integers IEEE754_extra.
From Hammer     Require Import Hammer Reconstr.
From Coq        Require Import ZArith.

Set Implicit Arguments.            Unset Strict Implicit.
Unset Printing Implicit Defensive. Set Bullet Behavior "None".

Module opt.
Fixpoint lift2 A B C (f:A->B->C) a b : option C :=
  match a,b with | Some a,Some b => Some(f a b)
                 | _,_ => None
  end.
Definition join    A  (a:option(option A)) := if a is Some a then a else None.
Definition bind   A B  (f:A->option B) a := if a is Some a then f a else None.
Definition bind2 A B C  (f:A->B->option C) a b: option C := join(lift2 f a b).
Definition map := option_map.
Notation "f =<< a" := (bind f a)(at level 40).
Notation "f <$> a" := (map f a)(at level 40).
End opt.

Module seqx.
Definition zipWith A B C (f: A->B->C) :=
  fix zipWith (s: seq A) (t: seq B) {struct s}: seq C :=
    match s, t with | [::],_ | _,[::] => [::]
                    | x::s, y::t => f x y :: zipWith s t end.

Definition seqOpt X (a:seq(option X)) : option(seq X) :=
  foldr (opt.lift2 cons) (Some[::]) a.
End seqx.


Module NE. Section NE.
Variables A B C : Type.
Inductive ne A := mk of A & seq A.

Definition sing (a:A) := mk a [::].
Definition map (f:A->B) (s:ne A):=
  let 'mk a aa:=s in mk (f a) (seq.map f aa).
Definition rev (s:ne A): ne A :=
  let 'mk a bb:=s in let r:=rcons(rev bb)a in mk(last a bb)(behead r).
Definition head '(mk a _) := a:A.
Definition tolist '(mk a aa) := a::aa : seq A.
Definition foldl (f:A->A->A) '(mk a aa) : A := foldl f a aa.
Definition seqOpt X (a:ne(option X)) : option(ne X) :=
  match a with NE.mk None _ => None
             | NE.mk (Some a) aa => if seqx.seqOpt aa is Some r
                                    then Some(NE.mk a r) else None
  end.
Definition zipWith (f:A->B->C) (a:ne A) (b:ne B): ne C :=
  let '(mk a aa, mk b bb) := (a,b) in mk (f a b) (seqx.zipWith f aa bb).


Remark wtf_last (a:A)(aa:seq A) :
  last(last a aa)(behead(rcons(seq.rev aa)a)) = a.
Proof.
rewrite -(revK aa); set r:=seq.rev aa; rewrite revK.
by case: r=> //= r rr; rewrite rev_cons last_rcons.
Qed.

Remark wtf_behead (a:A)(aa:seq A) :
  behead(rcons(seq.rev(behead(rcons(seq.rev aa)a))) (last a aa)) = aa.
Proof.
rewrite -(revK aa); set r:=seq.rev aa; rewrite revK.
case: r=> //= r rr. by rewrite rev_cons last_rcons rev_rcons rcons_cons.
Qed.

Lemma revK : involutive rev.
Proof. case=> //a l. by rewrite /rev wtf_last wtf_behead. Qed.
End NE. End NE.
Notation seq1:=NE.ne.


Module   I32:=Int.     Module   I64:=Int64.
Notation i32:=I32.int. Notation i64:=I64.int.
Notation "[i32 i ]" := (I32.mkint i _)(format "[i32  i ]").
Notation "[i64 i ]" := (I64.mkint i _)(format "[i64  i ]").


Inductive Nu := I of i32 | J of i64.
Inductive At := ANu of Nu | AC of ascii.
Inductive Ty := Ti|Tj|TL|Tc.
Inductive K :=
| A of At
| L of Ty & nat & seq1 K.


Definition nu2k    n := A(ANu n).             Coercion nu2k: Nu >-> K.
Definition nat2i32 n := I32.repr(Z.of_nat n). Coercion nat2i32: nat >-> i32.
Definition nat2i64 n := I64.repr(Z.of_nat n). Coercion nat2i64: nat >-> i64.



Section arith.
Definition ONi := I(I32.repr I32.min_signed).
Definition ONj := J(I64.repr I64.min_signed).

Definition Kiofnat (n:nat):K := I n.   Definition Kjofnat (n:nat):K := J n.

Definition iwiden (a:i32):i64 := I64.repr(I32.signed a).

Definition addnu (a b:Nu) := match a,b with
  | I i, I j => I(I32.add i j) | J i, J j => J(I64.add i j)
  | I i, J j => J(I64.add (iwiden i)j)
  | J i, I j => J(I64.add i(iwiden j)) end.

Definition eqnu (a b:Nu) := match a,b with
  | I i, I j => I32.eq i j | J i, J j => I64.eq i j
  | I i, J j => I64.eq (iwiden i)j
  | J i, I j => I64.eq i(iwiden j)
end.
Infix "=nu" := eqnu(at level 50).

Lemma wide_range a: (I64.min_signed <= I32.signed a <= I64.max_signed)%Z.
Admitted.


Lemma addnuC : commutative addnu.
Proof.
by elim=>i; elim=>j => /=; rewrite (I32.add_commut,I64.add_commut).
Qed.

Lemma addnu0i : right_id (I 0) addnu.
Proof.
elim=>i /=. by rewrite I32.add_zero.
by rewrite/iwiden I32.signed_zero I64.add_zero.
Qed.

Lemma addnu0j a : addnu a (J 0) =nu a.
Proof.
elim a=>i /=.
- by rewrite/iwiden I64.add_zero I64.eq_true.
by rewrite I64.add_zero I64.eq_true.
Qed.
End arith.

Definition K0j:K := J 0.  Definition K1j:K := J 1.
Definition K0i:K := I 0.  Definition K1i:K := I 1.

Definition K00i := L Ti 0 (NE.mk K0i  [::]).
Definition K31i := L Ti 3 (NE.mk K1i  [::K1i;K1i]).
Definition K331i:= L TL 3 (NE.mk K31i [::K31i;K31i]).
Definition K0C:K:= L Tc 0 (NE.sing (A(AC Space))).

Section ops.

Fixpoint map_a (f:At->option At) a: option K :=
  match a with
  | A n => opt.map A (f n)
  | L t n aa => opt.map (L t n) (NE.seqOpt (NE.map (map_a f) aa))
  end.

Fixpoint thread_a (f:At->At->option At) a b {struct a}: option K :=
  match a, b with
  | A a, A b     => opt.map A (f a b)
  | L _ _ _, A b => map_a (f^~b) a
  | A a, L _ _ _ => map_a (f a) b
  | L ta na a, L tb nb b =>
    if na==nb then
      opt.map (L ta na) (NE.seqOpt (NE.zipWith (thread_a f) a b))
    else None
  end.

Definition map_a' (f:At->At) (x:K) := map_a (Some \o f) x.
Definition thread_a' (f:At->At->At) (a b: K) :=
  thread_a (fun a b=> Some(f a b)) a b.

Definition add_a (a b:At): option At :=
  if (a,b) is (ANu a,ANu b) then Some(ANu(addnu a b)) else None.

Lemma add_aC (a b:At) : commutative add_a.
Proof.
case=>[i|c]; case=>[j|d] => //. by rewrite/add_a addnuC.
Qed.


Definition kadd (a b:K):option K := thread_a add_a a b.
Infix "+^" := kadd(at level 50).

Check erefl: I 2 +^ I 2 = Some(A(ANu(I 4))).


Lemma kaddA : associative (opt.bind2 kadd).
Admitted.


Definition ktype (a:K):Ty := match a with
| A(ANu(I _))=>Ti | A(ANu(J _))=>Tj | A(AC _)=>Tc | L _ _ _=> TL
end.


Definition ksize (a:K):K := match a with
| A a => K1i | L _ n _ => I n
end.

Notation "#: a"  := (ksize a)        (at level 60).
Notation "#:? a" := (opt.map ksize a)(at level 60).


Fixpoint nullify a := match a with
| A(ANu(I _))=> K0i
| A(ANu(J _))=> K0j
| A(AC _)=>     A(AC Space)
| L t n aa   => L t n (NE.map nullify aa)
end.


Definition unil:K := L TL 0 (NE.sing K0C).

Definition khead (k:K):K := match k with
| A _=> k | L t 0 a=> nullify (NE.head a) | L t n a=> NE.head a
end.

Notation "*:  a" := (khead a)        (at level 60).
Notation "*:? a" := (opt.map khead a)(at level 60).

Definition krev (k:K):K := match k with
| A _=> k | L t 0 a=> k | L t n aa=> L t n (NE.rev aa)
end.

Notation "|:  a" := (krev a)        (at level 60).
Notation "|:? a" := (opt.map krev a)(at level 60).


Lemma krevK : involutive krev.
Proof.
case=> t // n aa. case: n=> //= n. by rewrite NE.revK.
Qed.

Lemma size_krev a : (#:|:a) = #:a.
Proof. case: a=> // t n aa. case: n=> //. Qed.


Definition enlist (a:K):K := L TL 1 (NE.sing a).

Notation ",:" := (enlist)(at level 10).

Lemma size_enlist a : #:,:a = K1i.  Proof. by[]. Qed.



Definition krconst (a b:K):K := b.
Notation ":: a"  := (krconst a)(at level 60).
Notation "::? a" := (opt.map krconst a)(at level 60).

Definition izero := I32.eq 0.
Definition ipos  := I32.lt 0.  Definition ineg := I32.lt^~0.

Definition isI a := if a is A(ANu(I _)) then true else false.
Definition isIpos a := if a is A(ANu(I n)) then ipos n else false.

Definition kiota (a:K):option K := match a with
  | A(ANu(I ni))=>
    if izero ni then
      Some(L Ti 0 (NE.sing K0i))
    else if ipos ni then
      let n:=Z.to_nat (I32.signed ni)
      in Some(L Ti n (NE.mk K0i [seq Kiofnat i|i<-iota 1 n.-1]))
    else None
  | _=> None
end.

Notation "!: a"  := (kiota a)(at level 60).
Notation "!:? a" := (opt.bind kiota a)(at level 60).

Compute !:? K0i +^ K1i.



Lemma i_dec (a:i32) : {a=I32.zero}
                    + {izero a=false /\ ipos a /\ ineg a=false}
                    + {izero a=false /\ ipos a=false /\ ineg a}.
Admitted.



Lemma size_kiota a : isIpos a -> (#:?!:a) = Some a.
Proof.
case: a=> //= a. case: a => // n. case: n=> //i POS.
case: (i_dec i). case.
- scrush.
- case=> ->[] -> _ /=. rewrite/nat2i32 Z2Nat.id.
  + by rewrite Int.repr_signed.
  move:POS. rewrite/ipos.
  ryreconstr (@Z.lt_le_incl, @I32.signed_zero) (@is_true, @I32.lt).
scrush.
Qed.


(* Definition kfold (a f:K):K := match a with *)
(*   | A a=> a | L _ _ a aa=> foldl  *)


End ops.
