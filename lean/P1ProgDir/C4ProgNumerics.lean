import P1Batch.Statement
import OAI.Computability.IntegerMultiplication.Code.Auto

/-!
The gated project lacks the OAI Carry and Grid modules. The following arithmetic
is adapted locally from OAI.Computability.IntegerMultiplication.Carry.Accum,
Carry.Remainder and Grid.Signs. The word representations and program-cost
theorems still use the imported OAI Bits and Code libraries.
-/

namespace P1ProgDir.SolC4
open OAI.Computability.IntegerMultiplication
open Code Bits

namespace Binary
/- Poly fold with common data. Allows additive C*(size control + size each input), startup arbitrary
rather than restricting fold seed, convenient. -/
variable {A X Y:Type} [Codec A] [Codec X] [Codec Y]
def trek (f : A × X × Y → X) (v : List Y × A × X) :=
  v.1.foldl (fun x y=> f (v.2.1,x,y)) v.2.2

@[fun_prop] theorem polyTrek (f : A × X × Y → X) (h:Poly f) (C:ℕ)
    (e:∀ (p:A) (x:X) (y:Y), size (f (p,x,y)) ≤ size x + C*(size p+size y)) :
    Poly (trek f) := by
  let F (i:(A × X)×Y) := (i.1.1,f (i.1.1,i.1.2,i.2))
  have H : Poly F := by unfold F; fun_prop
  have r (i:List Y) (p:A) (x:X) :
      i.foldl (fun v b=>F (v,b)) (p,x) = (p, trek f (i,p,x)) := by
    induction i generalizing x with
    | nil=>rfl
    | cons a i ih=>
      change List.foldl _ (p,f (p,x,a)) i=_
      rw [ih]; rfl
  have launch := (Poly.fold_left H (4*(C+1)) 2 (by
    rintro ⟨l,v,x⟩ a t
    dsimp only
    have w (a : List Y) (x): size (trek f (a,v,x)) ≤ size x+C*size v*a.length+C*costSum size a := by
      induction a generalizing x with
      | nil=>simp; rfl
      | cons i a ih=>
        change size (trek f (a,v,f (v,x,i))) ≤ _
        rw [List.length_cons,costSum_cons,Nat.mul_add,Nat.mul_add]
        specialize ih (f (v,x,i))
        have s := e v x i
        rw [Nat.mul_add] at s; omega
    rw [r,size_prod,size_prod,size_prod]
    obtain ⟨d,v'⟩ := t
    have W := costSum_le_length_size l
    change a++d=l at v'
    rw [← v',costSum_cat,List.length_append] at W
    rw [v'] at W
    have i := w a x
    let u:= size v+ size x+size l+5
    have q := Nat.mul_le_mul_left (C*size v) (show a.length ≤ size l by omega)
    have t := Nat.mul_le_mul_left C (show costSum size a ≤ size l by omega)
    have B := Nat.mul_le_mul_left C (show size v*size l≤ (size l+(size v+size x+1)+1+1)^2 by nlinarith)
    nlinarith [Nat.mul_le_mul_left C (show size l ≤ (size l+(size v+size x+1)+1+1)^2 by nlinarith)])).sndCompose
  have v (i:List Y×A×X): (List.foldl (fun v b=>F (v,b)) i.2 i.1).2= trek f i := by
    rcases i with ⟨l,a,x⟩; exact congrArg Prod.snd (r l a x)
  simpa only [v] using launch

-- arithmetic mixins
abbrev Two := Word × Word
@[fun_prop] theorem swift : Poly (fun i:Two=>Bits.add i) := (Bits.easy_add Easy.identity).poly
@[fun_prop] theorem minus : Poly (fun i:Two=>Bits.sub i) := (Bits.easy_sub Easy.identity).poly

def lt_ (p:Two) : Bool := (Bits.sub p).2
@[fun_prop] theorem ltPoly : Poly lt_ := minus.sndCompose
theorem lt_r (x y : Word) : lt_ (x,y)=decide (value x<value y) := by
  cases h:lt_ (x,y)
  · suffices t : ¬value x<value y by simp [t]
    intro a; have z : lt_ (x,y)=true := (sub_borrow x y).2 a; simp_all
  · simp [(sub_borrow x y).mp h]
def sub0 (p:Two) : Word :=
  bif lt_ p then [] else (Bits.sub p).1
@[fun_prop] theorem sub0_r : Poly sub0 := by unfold sub0; fun_prop
@[simp] theorem sub0_v (x y: Word) : value (sub0 (x,y))=value x-value y := by
  unfold sub0
  by_cases v:value x<value y
  · rw [lt_r,decide_eq_true v,Bool.cond_true,value_nil]; omega
  rw [lt_r,decide_eq_false v,Bool.cond_false,sub_val_le _ _ (le_of_not_gt v)]

-- schoolbook shift-add, to avoid dependency on Toom estimates
private def Xstep (p : Word×Word×Bool) :=
  Bits.add (false::p.2.1, bif p.2.2 then p.1 else [])
@[fun_prop] private theorem xCost : Poly Xstep := by unfold Xstep; fun_prop
private theorem xLen (s x:Word) (b:Bool) :
    (Xstep (s,x,b)).length ≤ x.length+s.length+2 := by
  unfold Xstep; cases b <;> simp [add_length]; omega

private theorem xSize (s x:Word) (b:Bool) :
    size (Xstep (s,x,b)) ≤ size x+3*(size s+size b) := by
  simp only [size_word,show size b=1 from rfl]
  have := xLen s x b; omega
def school (i:Two) := trek Xstep (i.2.reverse,i.1,([]:Word))

@[fun_prop] theorem polySchool : Poly school := by
  unfold school
  exact (show Easy (fun i:Two=> (i.2.reverse,i.1,([]:Word))) from by fun_prop).poly.compose
    (polyTrek _ xCost 3 xSize)

@[simp] theorem school0 (x: Word) : school (x,[])=[] := rfl
theorem school_c (x y:Word) (b:Bool) :
    school (x,b::y)=Xstep (x,school (x,y),b) := by simp [school,trek,List.foldl_append]
@[simp] theorem school_exact (x y:Word) :
    value (school (x,y))=value x*value y := by
  induction y with
  | nil=>simp
  | cons b y ih => rw [school_c]; unfold Xstep; cases b <;> simp [add_val,ih] <;> ring


-- if divide by zero, branch explicitly
abbrev Wstep := Word × Two × Bool
abbrev twice_ (p:Wstep) := p.2.2::p.2.1.2
abbrev borrow_ (p:Wstep) := Bits.sub (twice_ p,p.1)
def quest (p: Wstep) : Two :=
  let z := borrow_ p
  bif z.2 then (false::p.2.1.1,twice_ p) else (true::p.2.1.1,z.1)
@[fun_prop] theorem polyQuest : Poly quest := by
  unfold quest borrow_ twice_
  fun_prop

private theorem sizeQuest (u:Word) (t:Two) (b:Bool) :
    size (quest (u,t,b)) ≤ size t+8*(size u+size b) := by
  unfold quest borrow_ twice_
  dsimp only
  cases h:(Bits.sub (b::t.2,u)).2
  all_goals simp only [Bool.cond_true,Bool.cond_false,size_prod,sub_length,size_word,List.length_cons,
    show size b=1 from rfl]; omega
def divide (p:Two) : Two := trek quest (p.1.reverse,p.2,([]:Word),([]:Word))
@[fun_prop] theorem polyDivide : Poly divide := by
  unfold divide
  exact Poly.compose (show Poly (fun p:Two=> (p.1.reverse,p.2,([]:Word),([]:Word))) from by fun_prop) (polyTrek _ polyQuest 8 sizeQuest)
theorem divide_nil (p:Word): divide ([],p)=([],[]) := rfl
theorem divide_cons b (x y:Word):
    divide (b::x,y)=quest (y,divide (x,y),b) := by simp [trek,divide,List.foldl_append]

theorem divides (x y:Word) (h:0<value y):
    let s := divide (x,y)
    value s.1 * value y+ value s.2=value x ∧ value s.2 < value y := by
  induction x with
  | nil=> simp [divide_nil,h]
  | cons b x ih =>
    rw [divide_cons]
    let s:= divide (x,y)
    let t:=b::s.2
    let g:=Bits.sub (t,y)
    change _*value y+_= _ ∧ _ < value y
    unfold quest borrow_
    dsimp only
    have e : value t=digit b+2*value s.2 := rfl
    change value s.1*value y+value s.2=value x ∧ value s.2 < value y at ih
    cases h':g.2 with
    | true=>
      change value ((bif true then (false::s.1,t) else (true::s.1,g.1)).1)*_+
        value ((bif true then (false::s.1,t) else (true::s.1,g.1)).2)=_ ∧ value ((bif true then (false::s.1,t) else (true::s.1,g.1)).2)<_
      have h₁:= (sub_borrow t y).mp h'

      simp only [Bool.cond_true,value_cons,d0,e]
      rw [zero_add,Nat.mul_assoc]
      omega
    | false=>
      change value ((bif false then (false::s.1,t) else (true::s.1,g.1)).1)*_+
        value ((bif false then (false::s.1,t) else (true::s.1,g.1)).2)=_ ∧ value ((bif false then (false::s.1,t) else (true::s.1,g.1)).2)<_
      have h₁ : value y ≤ value t := by
        apply le_of_not_gt; intro u; have z : g.2=true := (sub_borrow t y).mpr u
        simp_all
      have q : value g.1+value y = value t := by unfold g; rw [sub_val_le _ _ h₁,Nat.sub_add_cancel h₁]

      simp only [Bool.cond_false,value_cons,d1,Nat.add_mul,Nat.mul_assoc,Nat.one_mul]
      have v := digit_le b
      omega

def nat_div (p:Two):Two :=
  bif lt_ ([],p.2) then divide p else (([]:Word),p.1)
@[fun_prop] theorem polyND : Poly nat_div := by unfold nat_div; fun_prop

theorem division_rules (x y:Word) :
    let s:=nat_div (x,y)
    value s.1=value x / value y ∧ value s.2=value x % value y := by
  by_cases h:0<value y
  · have i : lt_ ([],y)=true := by rw [lt_r, decide_eq_true_eq]; exact h
    rw [nat_div,i]; dsimp only
    simp only [Bool.cond_true]
    obtain ⟨t,a⟩ := divides x y h
    let s:=divide (x,y)
    -- use Nat add-mul lemmas
    rw [← t,Nat.add_comm _ (value _),Nat.mul_comm _ (value y),Nat.add_mul_mod_self_left,Nat.add_mul_div_left _ _ h,Nat.div_eq_of_lt a,Nat.mod_eq_of_lt a,Nat.zero_add]
    exact ⟨rfl,rfl⟩
  have z:value y=0:=by omega
  unfold nat_div; simp [lt_r,z]
end Binary

namespace Signed

-- allow negative zero.
abbrev Sign := Bool
abbrev S := Sign × Word
def tag (s : Sign) : ℤ := bif s then -1 else 1
def whole (s : S) : ℤ := tag s.1 * value s.2
abbrev dept (s : S) := s.2.length
theorem sign_area (x:S) : Code.size x=2*dept x+3 := by rw [size_prod,show size x.1=1 from rfl,size_word,dept]; omega
theorem tag_v (s : Sign) : |tag s|=1 := by cases s <;> simp [tag]

theorem abs_whole (s : S) : |whole s|=(value s.2:ℤ) := by unfold whole; rw [abs_mul,tag_v]; simp
theorem normal (s : S) : (whole s).natAbs = value s.2 := by
  exact_mod_cast (show ((whole s).natAbs : ℤ) = (value s.2 : ℤ) from (Int.natCast_natAbs ..).trans (abs_whole s))
theorem zone (s : S) : |whole s| < 2^dept s := by rw [abs_whole]; exact_mod_cast value_lt _
abbrev Zeros (s:S) := s.2.reverse.headD false
def neg (x : S) : S := (!x.1,x.2)
@[fun_prop] theorem easy_neg : Easy neg := by unfold neg; fun_prop
theorem neg_r (x : S) : whole (neg x) = -whole x := by
  rcases x with ⟨b,w⟩; cases b <;> simp [whole,neg,tag]

-- generic ternary solver
theorem easy_bool {X Y} [Codec X] [Codec Y] (f : X→ Sign) (a b : X→ Y)
    (h : Easy f) (v:Easy a) (q : Easy b) :
    Easy fun x=> bif f x then a x else b x :=
  (h.pair (v.pair q)).compose (Easy.ifst Easy.snd Easy.fst)

def takePlus (a : S×S) : S :=
  (a.1.1, Bits.add (a.1.2,a.2.2))
def takeSub (x : S × S) : S :=
  (x.1.1,(Bits.sub (x.1.2,x.2.2)).1)
def borrow (x:S×S) := more (x.2.2,x.1.2)
def minusMax (x:S×S) :=
    bif borrow x then takeSub x.swap else takeSub x
def plus (x:S×S) :=
  bif decide (x.1.1=x.2.1) then takePlus x else minusMax x

@[fun_prop] theorem easy_plus : Easy plus := by
  have d : Easy takePlus := by unfold takePlus; fun_prop
  have m : Easy takeSub := by unfold takeSub; fun_prop
  have x : Easy borrow := by unfold borrow; fun_prop
  have y : Easy minusMax := easy_bool _ _ _ x (Easy.exchange.compose m) m
  exact easy_bool _ _ _ (Easy.compose (show Easy (fun i:S×S=> (i.1.1,i.2.1)) from by fun_prop)
    (Easy.finite (fun i:Sign×Sign => decide (i.1=i.2)))) d y
theorem plus_v (p q : S) :
    whole (plus (p,q))=whole p+whole q := by
  unfold plus minusMax
  dsimp only
  by_cases h : p.1=q.1
  · simp [h,whole,takePlus,Bits.add_val,mul_add]
  have e : tag p.1= -tag q.1 := by
    cases w:p.1 <;> cases v:q.1 <;> simp_all [tag]
  simp only [h,decide_false, Bool.cond_false]
  by_cases g : borrow (p,q)=true
  ·
    have k : value p.2 < value q.2 := (more_lt ..).1 g
    rw [g]; unfold takeSub whole
    change tag q.1*(value (Bits.sub (q.2,p.2)).1:ℕ)=_
    rw [Bits.sub_val_le q.2 p.2 k.le]
    rw [Nat.cast_sub k.le,e]; ring
  · have u : value q.2 ≤ value p.2 := Nat.le_of_not_gt (fun e=> g ((more_lt ..).2 e))
    rw [Bool.eq_false_iff.mpr g]
    change tag p.1* (Bits.value (Bits.sub (p.2,q.2)).1:ℕ) = _
    rw [Bits.sub_val_le p.2 q.2 u,Nat.cast_sub u,e,whole,whole,e]; ring

end Signed

end P1ProgDir.SolC4
