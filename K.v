(******************************************************************************)
(*  eq* eqType  aeq* K's =                                                    *)
(*  +: monadic  +, dyadic  +? in k-monad                                      *)
(******************************************************************************)
From mathcomp   Require Import ssreflect ssrnat ssrbool ssrfun eqtype seq.
From QuickChick Require Import QuickChick.
From compcert   Require Import Integers IEEE754_extra.
From Hammer     Require Import Hammer Reconstr.
From Coq        Require Import ZArith.

Set Implicit Arguments.            Unset Strict Implicit.
Unset Printing Implicit Defensive. Set Bullet Behavior "None".

Notation"[ 'rw' r ]" :=
                   (ltac:(rewrite r))(at level 0,r at level 0):ssripat_scope.

Lemma swap_forall A B (P:A->B->Type): (forall x y, P x y)->forall y x, P x y.
Proof. firstorder. Qed.             Notation "[ 'sw' l ]" := (swap_forall l).

Module opt.
Fixpoint lift2 A B C (f:A->B->C) a b : option C :=
  match a,b with | Some a,Some b => Some(f a b)
                 | _,_ => None
  end.
Definition join    A  (a:option(option A)) := if a is Some a then a else None.
Definition bind   A B  (f:A->option B) a := if a is Some a then f a else None.
Definition bind2 A B C  (f:A->B->option C) a b: option C := join(lift2 f a b).
Notation "f =<< a" := (obind f a)(at level 40).
Notation "f <$> a" := (omap f a) (at level 40).
End opt.

Module seqx.
Definition zipWith A B C (f: A->B->C) :=
  fix zw (s: seq A) (t: seq B) {struct s}: seq C :=
    match s, t with | [::],_ | _,[::] => [::]
                    | x::s, y::t => f x y :: zw s t end.
Definition seqOpt X (a:seq(option X)) : option(seq X) :=
  foldr (opt.lift2 cons) (Some[::]) a.
Definition all2 {A B} (r:A->B->bool) := fix all2 s t :=
  match s, t with [::],[::]=>true | a::s,b::t=>r a b && all2 s t | _,_=>false
  end.
Definition travOpt A B (f:A->option B) s := seqOpt [seq f a|a<-s].

Remark zipWithC A B (f:A->A->B) : commutative f -> commutative (zipWith f).
Proof. move=>C. elim=>[|a l I]; case=>//=b t. by rewrite C I. Qed.
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
Definition foldr (f:A->A->A) '(mk a aa) : A := foldr f a aa.
Definition seqOpt X (a:ne(option X)) : option(ne X) :=
  match a with NE.mk None _ => None
             | NE.mk (Some a) aa => if seqx.seqOpt aa is Some r
                                    then Some(NE.mk a r) else None
  end.
Definition zipWith (f:A->B->C) (a:ne A) (b:ne B): ne C :=
  let '(mk a aa, mk b bb) := (a,b) in mk (f a b) (seqx.zipWith f aa bb).
Definition all2 (e:A->B->bool) (a:ne A) (b:ne B) :=
  let '(mk a aa, mk b bb) := (a,b) in e a b && seqx.all2 e aa bb.

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

Lemma eq_map f g : f =1 g -> map f =1 map g.
Proof.
move=>F. case=>a l. elim:l=> [|x l I] /=; rewrite !F//. by rewrite (eq_map F).
Qed.
End NE. End NE.
Notation seq1:=NE.ne.


Module   I32:=Int.     Module   I64:=Int64.
Notation i32:=I32.int. Notation i64:=I64.int.
Notation "[i32 i ]" := (I32.mkint i _)(format "[i32  i ]").
Notation "[i64 i ]" := (I64.mkint i _)(format "[i64  i ]").


Section core.

Inductive Nu := I of i32 | J of i64.
Inductive At := ANu of Nu | AC of ascii.
Inductive Ty := Ti|Tj|TL|Tc.

Unset Elimination Schemes.
Inductive K := A of At | L of Ty & nat & seq1 K.

Definition K_ind
   (P:  K->Prop)
   (IA: forall a:At, P(A a))
   (IL: forall (t:Ty)(n:nat)(a:K)(s:seq K),
       foldr (fun x:K => and(P x)) True (a::s) -> P (L t n (NE.mk a s))) :=
 fix loop a: P a: Prop := match a with
 | A a => IA a
 | L t n (NE.mk a0 s0) =>
    let fix all s : foldr (fun x => and (P x)) True s :=
      if s is e::s then conj (loop e) (all s) else Logic.I
    in IL t n a0 s0 (all (a0::s0))
 end.                                               Set Elimination Schemes.


Definition nu2k    n := A(ANu n).             Coercion nu2k: Nu >-> K.
Definition nat2i32 n := I32.repr(Z.of_nat n). Coercion nat2i32: nat >-> i32.
Definition nat2i64 n := I64.repr(Z.of_nat n). Coercion nat2i64: nat >-> i64.

End core.


Section kburrito.
Inductive oops:= EType|EClass|EDom|ELen.
Inductive res:=   Err of oops|OK of K.
End kburrito.

Section arith.
Definition ONi := I(I32.repr I32.min_signed).
Definition ONj := J(I64.repr I64.min_signed).

Definition Kiofnat (n:nat):K := I n.   Definition Kjofnat (n:nat):K := J n.

Definition iwiden (a:i32):i64 := I64.repr(I32.signed a).

Definition addnu (a b:Nu) := match a,b with
  | I i, I j => I(I32.add i j) | J i, J j => J(I64.add i j)
  | I i, J j => J(I64.add (iwiden i)j)
  | J i, I j => J(I64.add i(iwiden j)) end.

Definition aeqnu (a b:Nu) := match a,b with
  | I i, I j => I32.eq i j | J i, J j => I64.eq i j
  | I i, J j => I64.eq (iwiden i)j
  | J i, I j => I64.eq i(iwiden j)
end.
Infix "=nu" := aeqnu(at level 50).

Lemma aeqnuC : symmetric aeqnu.
Proof. by case=>i; case=>j=> /=; rewrite (I32.eq_sym,I64.eq_sym). Qed.

Definition eqnu (a b:Nu) := match a,b with
  | I i,I j=>I32.eq i j | J i,J j=>I64.eq i j | _,_=>false
end.

Lemma i32P : Equality.axiom I32.eq.
Proof.
by move=>*; apply:(iffP idP)=>[/I32.same_if_eq|->/[rw I32.eq_true]].
Qed.

Lemma i64P : Equality.axiom I64.eq.
Proof.
by move=>*; apply:(iffP idP)=>[/I64.same_if_eq|->/[rw I64.eq_true]].
Qed.

Canonical i32_eqMixin := EqMixin i32P.   Canonical i64_eqMixin := EqMixin i64P.
Canonical i32_eqType := Eval hnf in EqType i32 i32_eqMixin.
Canonical i64_eqType := Eval hnf in EqType i64 i64_eqMixin.

Lemma eqnuP : Equality.axiom eqnu.
Proof.
move=>a b. apply:(iffP idP)=>[|->].
- case:a=>i; case:b=>j//=. by move/i32P->. by move/i64P->.
case:b=>j/=. exact/i32P. exact/i64P.
Qed.

Canonical Nu_eqMixin := EqMixin eqnuP.
Canonical Nu_eqType  := Eval hnf in EqType Nu Nu_eqMixin.

Lemma eqnuE : eqnu=eq_op.     Proof. by[]. Qed.
Lemma eqnuC : symmetric eqnu. Proof. by move=>*/[rw eqnuE]. Qed.

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

Section eq.

Definition eqat a b: bool := match a,b with
  | ANu a,ANu b=> a==b | AC a,AC b=> Ascii.eqb a b | _,_=> false
end.

Lemma eqatP : Equality.axiom eqat.
Proof.
move=>a b. apply:(iffP idP)=>[|->]. case:a=>[n|a]; case:b=>[m|b]//=.
by move/eqP->. by move/Ascii.eqb_spec->. case:b=>//=b. exact:Ascii.eqb_refl.
Qed.
Canonical At_eqMixin := EqMixin eqatP.
Canonical At_eqType  := Eval hnf in EqType At At_eqMixin.

Lemma eqatE : eqat=eq_op.     Proof. by[]. Qed.
Lemma eqatC : symmetric eqat. Proof. by move=>*/[rw eqatE]. Qed.

Definition aeqat a b: bool := match a,b with
  | ANu a,ANu b=> aeqnu a b | AC a,AC b=> Ascii.eqb a b | _,_=> false
end.

Remark aeqatC : symmetric aeqat.
Proof. case=>[x|a]; case=>[y|b]//=. exact:aeqnuC. exact:Ascii.eqb_sym. Qed.

Definition eqty a b :=
  match a,b with Ti,Ti|Tj,Tj|TL,TL|Tc,Tc=>true|_,_=>false end.
Lemma eqtyP : Equality.axiom eqty.
Proof. move=>a b. apply:(iffP idP)=>[|->]. by case:a;case:b. by case:b. Qed.
Canonical Ty_eqMixin := EqMixin eqtyP.
Canonical Ty_eqType  := Eval hnf in EqType Ty Ty_eqMixin.

Fixpoint eqk (a b:K) {struct a} := match a,b with
  | A a, A b=> a==b
  | L t n s, L t' n' s'=> [&& t==t', n==n' & NE.all2 eqk s s']
  | _,_=> false
end.

Lemma eqkP : Equality.axiom eqk.
Proof.
move=> x y; apply: (iffP idP)=> [|->].
- elim: x y=>[a[]//=?/eqP->//|t n a s Ixs [|t' n'[]a' s']//=].
  move/and3P=>[]/eqP->/eqP->.
  elim: s Ixs s'=> /=.
  + case=>I _ []; first by move/andP=>[]/I->. move=>a0 s0. by move/andP=>[]/I.
  rewrite/NE.all2/= =>a0 s0 I[] J[] H F[]; first by move/andP=>[].
  move=>??. move/and3P=>[Q+]/(conj Q)/andP/(I _). scrush.
elim: y=>//=t n a; elim. rewrite/NE.all2/=. case. move->=>_. exact/and3P.
scrush.
Qed.

Canonical K_eqMixin := EqMixin eqkP.
Canonical K_eqType  := Eval hnf in EqType K K_eqMixin.

End eq.

Section qc_wish.
Instance geni32 : GenSized i32 :=
  {| arbitrarySized _ := returnGen (I32.repr 0) |}.
Instance geni64 : GenSized i64 :=
  {| arbitrarySized _ := returnGen (I64.repr 0) |}.
Instance shri32 : Shrink i32 := {| shrink _ := nil |}.
Instance shri64 : Shrink i64 := {| shrink _ := nil |}.

Instance Showi32 : Show i32 := {| show '[i32 i] := show i |}.
Instance Showi64 : Show i64 := {| show '[i64 i] := show i |}.
Instance Showseq1 T : Show (seq1 T) := {| show s := "<seq>"%string |}.

Derive (Arbitrary,Show) for ascii.
Derive (Arbitrary,Show) for Ty.         Derive (Arbitrary,Show) for Nu.
Derive (Arbitrary,Show) for At.         Derive Show for K.

Import QcDefaultNotation.

Global Instance gensK : GenSized K :=
  {| arbitrarySized _ := freq [(1, returnGen K0i)] |}.
Global Instance shrinkK : Shrink K := {| shrink _ := nil |}.
End qc_wish.


Section ops.

Fixpoint map_a (f:At->option At) a: option K :=
  match a with
  | A n => omap A (f n)
  | L t n aa => omap (L t n) (NE.seqOpt (NE.map (map_a f) aa))
  end.

Fixpoint thread_a (f:At->At->option At) a b {struct a}: option K :=
  match a, b with
  | A a, A b     => omap A (f a b)
  | L _ _ _, A b => map_a (f^~b) a
  | A a, L _ _ _ => map_a (f a) b
  | L ta na a, L tb nb b =>
    if na==nb then
      omap (L ta na) (NE.seqOpt (NE.zipWith (thread_a f) a b))
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

Notation "#: a"  := (ksize a)     (at level 60).
Notation "#:? a" := (omap ksize a)(at level 60).


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

Notation "*:  a" := (khead a)     (at level 60).
Notation "*:? a" := (omap khead a)(at level 60).

Definition krev (k:K):K := match k with
| A _=> k | L t 0 a=> k | L t n aa=> L t n (NE.rev aa)
end.

Notation "|:  a" := (krev a)     (at level 60).
Notation "|:? a" := (omap krev a)(at level 60).


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
Notation ":: a"  := (krconst a)     (at level 60).
Notation "::? a" := (omap krconst a)(at level 60).

Definition izero := I32.eq 0.
Definition ipos  := I32.lt 0.  Definition ineg := I32.lt^~0.

Definition isI a := if a is A(ANu(I _)) then true else false.
Definition isIpos a := if a is A(ANu(I n)) then ipos n else false.

Definition iiota (n:nat):seq nat := iota 0 n.

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

Notation "!: a"  := (kiota a)      (at level 60).
Notation "!:? a" := (obind kiota a)(at level 60).

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

Fixpoint iwhere' (i:nat) (s:seq nat) :=
  if s is a::s then nseq a i ++ iwhere' i.+1 s else [::].
Definition iwhere := iwhere' 0.

Lemma iwhere'S i s : iwhere' i.+1 s = [seq a.+1 | a<-iwhere' i s].
Proof.
  elim:s i=>//=[n]s I i. by rewrite map_cat -I map_nseq.
Qed.

Lemma iwhere_x a : iwhere [::a] = nseq a 0.
Proof.
by rewrite/iwhere/iwhere'/= cats0.
Qed.

Lemma iwhere_cons a s : iwhere(a::s) = nseq a 0 ++ [seq e.+1 | e<-iwhere s].
Proof.
by rewrite/iwhere/=iwhere'S.
Qed.

Lemma iwhere_ones a b : iwhere' a (nseq b 1) = iota a b.
Proof.
elim:b=>//=b. rewrite/iwhere/=iwhere'S=>->. by rewrite -[a.+1]add1n iota_addl.
Qed.

Lemma iwhere_where_xy a b : (iwhere \o iwhere) [::a;b] = iota a b.
Proof.
rewrite/comp/iwhere/=cats0. elim:a=>/=[|a]; first by rewrite iwhere_ones.
rewrite iwhere'S=>->. by rewrite -[a.+1]add1n iota_addl.
Qed.

Lemma iwhere_size s : size (iwhere s) = sumn s.
elim:s=>//=a s I. by rewrite iwhere_cons size_cat -I size_nseq size_map.
Qed.

Remark seqxxx ls s : [seq e + s.+1 | e <- ls] = [seq e.+1 + s | e <- ls].
Proof. exact/eq_map/[sw addnS]. Qed.

Lemma iwhere_cat s t : iwhere(s++t) = iwhere s ++ [seq e+size s|e<-iwhere t].
Proof.
elim:t s=>//=[s|a l I s]; first by rewrite ?cats0.
rewrite iwhere_cons map_cat -map_comp.
rewrite/iwhere in I*.
rewrite -cat_rcons. rewrite I.
rewrite size_rcons. rewrite seqxxx. rewrite catA. congr(_++_).
elim:s=>//[|b s].
- rewrite/=cats0. elim:a=>//=a/[rw add0n]->.
  rewrite -map_comp. congr(_::_). elim:nseq=>//=>[->]; by rewrite -addnA.
rewrite rcons_cons -/iwhere !iwhere_cons -catA. move->. rewrite map_cat.
congr(_++_). rewrite seqxxx. rewrite -map_comp. elim:nseq=>//.
Qed.

Program Fixpoint itakep_ A(n:nat)(s:seq A){measure n}: seq A :=
  if s isn't [::] then
    (if n <= size s as r return (n <= size s = r -> _)
       then fun pf => take n s
       else fun pf => s ++ itakep_ (n - size s) s) erefl
  else [::].
Next Obligation.
apply/ltP. move:H pf. case:s=>//=a l _. rewrite ltn_subrL. scrush.
Defined.

From mathcomp Require Import div.

Definition itakep__ A(n:nat)(s:seq A) :=
  if s isn't[::]then flatten(nseq (n %/ size s) s) ++ take (n %% size s) s
  else[::].

Definition itakep A(n:nat)(z:A)(s:seq A):seq A :=
  if s isn't[::]then take n(flatten(nseq n s))
  else nseq n z.


Definition itaken A(n:nat)(s:seq A):= drop (size s-n) s.

Definition itake A(n:int)(z:A)(s:seq A):= match n with
 Posz n=> if s isn't [::] then itakep n z s else nseq n z | Negz n=> itaken n s
end.

Lemma size_takep A n z (s:seq A) : size (itakep n z s) = `|n|.
Proof.
case:s=>[/[rw size_nseq]//|a s]. rewrite size_takel//.
elim:n=>//n. rewrite -addn1 nseq_addn/=. rewrite flatten_cat size_cat/=cats0/=.
move/leq_add. exact.
Qed.

(* Definition kfold (a f:K):K := match a with *)
(*   | A a=> a | L _ _ a aa=> foldl  *)


End ops.
