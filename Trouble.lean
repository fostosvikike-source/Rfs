namespace RSFLean

inductive ZigError : Type where
  | overflow : ZigError
  | nonFinite : ZigError
  | invalidConfig : ZigError
  | invalidDimension : ZigError
  | invalidLayerCount : ZigError
  | invalidBatchSize : ZigError
  | invalidTolerance : ZigError
  | shapeMismatch : ZigError
  | dataLengthMismatch : ZigError
  | aliasedBuffers : ZigError
  | notInitialized : ZigError
  | handleCopied : ZigError
  | tooLarge : ZigError
  | invalidModelState : ZigError
  | gpuUnsupportedConfiguration : ZigError
  | noGPUAvailable : ZigError
  | numericFailure : ZigError
  | badFileFormat : ZigError
  | unsupportedVersion : ZigError
  | checksumMismatch : ZigError
  | trailingData : ZigError
  | tempFileCollision : ZigError

inductive ResultT (α : Type) : Type where
  | ok : α → ResultT α
  | err : ZigError → ResultT α

def ResultT.bind {α β : Type} (x : ResultT α) (f : α → ResultT β) : ResultT β :=
  ResultT.recOn (motive := fun _ => ResultT β) x
    (fun v => f v)
    (fun e => ResultT.err e)

def ResultT.map {α β : Type} (f : α → β) (x : ResultT α) : ResultT β :=
  ResultT.recOn (motive := fun _ => ResultT β) x
    (fun v => ResultT.ok (f v))
    (fun e => ResultT.err e)

def ResultT.isOk {α : Type} (x : ResultT α) : Bool :=
  ResultT.recOn (motive := fun _ => Bool) x (fun _ => Bool.true) (fun _ => Bool.false)

def ResultT.isErr {α : Type} (x : ResultT α) : Bool :=
  ResultT.recOn (motive := fun _ => Bool) x (fun _ => Bool.false) (fun _ => Bool.true)

theorem ResultT.bind_ok_eq {α β : Type} (v : α) (f : α → ResultT β) :
    ResultT.bind (ResultT.ok v) f = f v := Eq.refl (f v)

theorem ResultT.bind_err_eq {α β : Type} (e : ZigError) (f : α → ResultT β) :
    ResultT.bind (ResultT.err e) f = ResultT.err e := Eq.refl (ResultT.err e)

theorem ResultT.map_ok_eq {α β : Type} (f : α → β) (v : α) :
    ResultT.map f (ResultT.ok v) = ResultT.ok (f v) := Eq.refl (ResultT.ok (f v))

theorem ResultT.map_err_eq {α β : Type} (f : α → β) (e : ZigError) :
    ResultT.map f (ResultT.err e) = ResultT.err e := Eq.refl (ResultT.err e)

theorem ResultT.right_id {α : Type} (x : ResultT α) :
    ResultT.bind x (fun v => ResultT.ok v) = x :=
  ResultT.recOn
    (motive := fun y => ResultT.bind y (fun v => ResultT.ok v) = y) x
    (fun v => Eq.refl (ResultT.ok v))
    (fun e => Eq.refl (ResultT.err e))

theorem ResultT.left_id {α β : Type} (v : α) (f : α → ResultT β) :
    ResultT.bind (ResultT.ok v) f = f v := Eq.refl (f v)

theorem ResultT.assoc {α β γ : Type} (x : ResultT α) (f : α → ResultT β) (g : β → ResultT γ) :
    ResultT.bind (ResultT.bind x f) g = ResultT.bind x (fun v => ResultT.bind (f v) g) :=
  ResultT.recOn
    (motive := fun y => ResultT.bind (ResultT.bind y f) g
               = ResultT.bind y (fun v => ResultT.bind (f v) g))
    x
    (fun v => Eq.refl (ResultT.bind (f v) g))
    (fun e => Eq.refl (ResultT.err e))

theorem ResultT.map_compose {α β γ : Type} (f : α → β) (g : β → γ) (x : ResultT α) :
    ResultT.map g (ResultT.map f x) = ResultT.map (fun v => g (f v)) x :=
  ResultT.recOn
    (motive := fun y => ResultT.map g (ResultT.map f y)
               = ResultT.map (fun v => g (f v)) y)
    x
    (fun v => Eq.refl (ResultT.ok (g (f v))))
    (fun e => Eq.refl (ResultT.err e))

theorem ResultT.bind_map {α β γ : Type} (f : α → β) (g : β → ResultT γ) (x : ResultT α) :
    ResultT.bind (ResultT.map f x) g = ResultT.bind x (fun v => g (f v)) :=
  ResultT.recOn
    (motive := fun y => ResultT.bind (ResultT.map f y) g = ResultT.bind y (fun v => g (f v)))
    x
    (fun v => Eq.refl (g (f v)))
    (fun e => Eq.refl (ResultT.err e))

def bNot (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) Bool.true Bool.false b

def bAnd (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) Bool.false b a

def bOr (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) b Bool.true a

def bXor (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) b (bNot b) a

def bEq (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (bNot b) b a

def bIte {α : Type} (b : Bool) (t e : α) : α :=
  Bool.rec (motive := fun _ => α) e t b

theorem bIte_true {α : Type} (t e : α) : bIte Bool.true t e = t := Eq.refl t
theorem bIte_false {α : Type} (t e : α) : bIte Bool.false t e = e := Eq.refl e

theorem bNot_true : bNot Bool.true = Bool.false := Eq.refl Bool.false
theorem bNot_false : bNot Bool.false = Bool.true := Eq.refl Bool.true
theorem bNot_involutive (b : Bool) : bNot (bNot b) = b :=
  Bool.rec (motive := fun x => bNot (bNot x) = x)
    (Eq.refl Bool.false) (Eq.refl Bool.true) b

theorem bAnd_false_l (b : Bool) : bAnd Bool.false b = Bool.false := Eq.refl Bool.false
theorem bAnd_true_l (b : Bool) : bAnd Bool.true b = b := Eq.refl b
theorem bAnd_false_r (b : Bool) : bAnd b Bool.false = Bool.false :=
  Bool.rec (motive := fun x => bAnd x Bool.false = Bool.false)
    (Eq.refl Bool.false) (Eq.refl Bool.false) b
theorem bAnd_true_r (b : Bool) : bAnd b Bool.true = b :=
  Bool.rec (motive := fun x => bAnd x Bool.true = x)
    (Eq.refl Bool.false) (Eq.refl Bool.true) b
theorem bAnd_comm (a b : Bool) : bAnd a b = bAnd b a :=
  Bool.rec (motive := fun x => bAnd x b = bAnd b x)
    (Eq.trans (bAnd_false_l b) (Eq.symm (bAnd_false_r b)))
    (Eq.trans (bAnd_true_l b) (Eq.symm (bAnd_true_r b)))
    a
theorem bAnd_assoc (a b c : Bool) : bAnd (bAnd a b) c = bAnd a (bAnd b c) :=
  Bool.rec (motive := fun x => bAnd (bAnd x b) c = bAnd x (bAnd b c))
    (Eq.trans (congrArg (fun y => bAnd y c) (bAnd_false_l b))
              (Eq.trans (bAnd_false_l c) (Eq.symm (bAnd_false_l (bAnd b c)))))
    (Eq.trans (congrArg (fun y => bAnd y c) (bAnd_true_l b))
              (Eq.symm (bAnd_true_l (bAnd b c))))
    a

theorem bOr_false_l (b : Bool) : bOr Bool.false b = b := Eq.refl b
theorem bOr_true_l (b : Bool) : bOr Bool.true b = Bool.true := Eq.refl Bool.true
theorem bOr_false_r (b : Bool) : bOr b Bool.false = b :=
  Bool.rec (motive := fun x => bOr x Bool.false = x)
    (Eq.refl Bool.false) (Eq.refl Bool.true) b
theorem bOr_true_r (b : Bool) : bOr b Bool.true = Bool.true :=
  Bool.rec (motive := fun x => bOr x Bool.true = Bool.true)
    (Eq.refl Bool.true) (Eq.refl Bool.true) b
theorem bOr_comm (a b : Bool) : bOr a b = bOr b a :=
  Bool.rec (motive := fun x => bOr x b = bOr b x)
    (Eq.trans (bOr_false_l b) (Eq.symm (bOr_false_r b)))
    (Eq.trans (bOr_true_l b) (Eq.symm (bOr_true_r b)))
    a

def boolFalseNeTrue (h : Bool.false = Bool.true) : False :=
  Eq.mp
    (congrArg (fun b => Bool.rec (motive := fun _ => Prop) True False b) h)
    True.intro

def boolTrueNeFalse (h : Bool.true = Bool.false) : False :=
  boolFalseNeTrue (Eq.symm h)

def natPred (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun m _ => m) n

def natSub (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) a (fun _ ih => natPred ih) b

def natEqB : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool)
    (Nat.rec (motive := fun _ => Bool) Bool.true (fun _ _ => Bool.false))
    (fun _ ih b =>
      Nat.rec (motive := fun _ => Bool) Bool.false (fun b' _ => ih b') b)

def natLeB : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool)
    (fun _ => Bool.true)
    (fun _ ih b =>
      Nat.rec (motive := fun _ => Bool) Bool.false (fun b' _ => ih b') b)

def natLtB (a b : Nat) : Bool := natLeB (Nat.succ a) b

def natMin (a b : Nat) : Nat := bIte (natLeB a b) a b
def natMax (a b : Nat) : Nat := bIte (natLeB a b) b a

theorem natPred_zero : natPred 0 = 0 := Eq.refl 0
theorem natPred_succ (n : Nat) : natPred (Nat.succ n) = n := Eq.refl n
theorem natSub_zero (a : Nat) : natSub a 0 = a := Eq.refl a
theorem natSub_succ (a b : Nat) : natSub a (Nat.succ b) = natPred (natSub a b) := Eq.refl _

theorem natEqB_zero_zero : natEqB 0 0 = Bool.true := Eq.refl Bool.true
theorem natEqB_zero_succ (n : Nat) : natEqB 0 (Nat.succ n) = Bool.false := Eq.refl Bool.false
theorem natEqB_succ_zero (n : Nat) : natEqB (Nat.succ n) 0 = Bool.false := Eq.refl Bool.false
theorem natEqB_succ_succ (a b : Nat) :
    natEqB (Nat.succ a) (Nat.succ b) = natEqB a b := Eq.refl _
theorem natEqB_refl (n : Nat) : natEqB n n = Bool.true :=
  Nat.recOn (motive := fun m => natEqB m m = Bool.true) n
    (Eq.refl Bool.true)
    (fun _ ih => ih)
theorem natEqB_symm (a b : Nat) : natEqB a b = natEqB b a :=
  Nat.recOn
    (motive := fun x => (y : Nat) → natEqB x y = natEqB y x) a
    (fun y => Nat.recOn (motive := fun z => natEqB 0 z = natEqB z 0) y
      (Eq.refl Bool.true)
      (fun _ _ => Eq.refl Bool.false))
    (fun a' ih y =>
      Nat.recOn (motive := fun z => natEqB (Nat.succ a') z = natEqB z (Nat.succ a')) y
        (Eq.refl Bool.false)
        (fun b' _ => ih b'))
    b

theorem natLeB_zero (n : Nat) : natLeB 0 n = Bool.true := Eq.refl Bool.true
theorem natLeB_succ_zero (n : Nat) : natLeB (Nat.succ n) 0 = Bool.false := Eq.refl Bool.false
theorem natLeB_succ_succ (a b : Nat) :
    natLeB (Nat.succ a) (Nat.succ b) = natLeB a b := Eq.refl _
theorem natLeB_refl (n : Nat) : natLeB n n = Bool.true :=
  Nat.recOn (motive := fun m => natLeB m m = Bool.true) n
    (Eq.refl Bool.true)
    (fun _ ih => ih)
theorem natLtB_irrefl (n : Nat) : natLtB n n = Bool.false :=
  Nat.recOn (motive := fun m => natLtB m m = Bool.false) n
    (Eq.refl Bool.false)
    (fun _ ih => ih)
theorem natLeB_succ (n : Nat) : natLeB n (Nat.succ n) = Bool.true :=
  Nat.recOn (motive := fun m => natLeB m (Nat.succ m) = Bool.true) n
    (Eq.refl Bool.true)
    (fun _ ih => ih)
theorem natLeB_trans (a b c : Nat)
    (h1 : natLeB a b = Bool.true) (h2 : natLeB b c = Bool.true) :
    natLeB a c = Bool.true :=
  (Nat.recOn
    (motive := fun a =>
      (b c : Nat) → natLeB a b = Bool.true → natLeB b c = Bool.true → natLeB a c = Bool.true)
    a
    (fun _ _ _ _ => Eq.refl Bool.true)
    (fun a' iha b =>
      Nat.recOn
        (motive := fun b =>
          (c : Nat) → natLeB (Nat.succ a') b = Bool.true → natLeB b c = Bool.true
                      → natLeB (Nat.succ a') c = Bool.true)
        b
        (fun _ k1 _ => False.elim (boolFalseNeTrue k1))
        (fun b' _ c =>
          Nat.recOn
            (motive := fun c =>
              natLeB (Nat.succ a') (Nat.succ b') = Bool.true →
              natLeB (Nat.succ b') c = Bool.true →
              natLeB (Nat.succ a') c = Bool.true)
            c
            (fun _ k2 => False.elim (boolFalseNeTrue k2))
            (fun c' _ k1 k2 => iha b' c' k1 k2))))
  b c h1 h2

inductive FixedQ : Type where
  | nonneg : Nat → FixedQ
  | negsucc : Nat → FixedQ

def FixedQ.zero : FixedQ := FixedQ.nonneg 0
def FixedQ.one : FixedQ := FixedQ.nonneg 1
def FixedQ.negOne : FixedQ := FixedQ.negsucc 0
def FixedQ.ofNat (n : Nat) : FixedQ := FixedQ.nonneg n

def FixedQ.neg (x : FixedQ) : FixedQ :=
  FixedQ.recOn (motive := fun _ => FixedQ) x
    (fun n =>
      Nat.recOn (motive := fun _ => FixedQ) n
        (FixedQ.nonneg 0)
        (fun n' _ => FixedQ.negsucc n'))
    (fun n => FixedQ.nonneg (Nat.succ n))

def FixedQ.isFinite (_ : FixedQ) : Bool := Bool.true

def FixedQ.isZero (x : FixedQ) : Bool :=
  FixedQ.recOn (motive := fun _ => Bool) x
    (fun n => natEqB n 0)
    (fun _ => Bool.false)

def FixedQ.eqB (a b : FixedQ) : Bool :=
  FixedQ.recOn (motive := fun _ => Bool) a
    (fun n1 =>
      FixedQ.recOn (motive := fun _ => Bool) b
        (fun n2 => natEqB n1 n2)
        (fun _ => Bool.false))
    (fun n1 =>
      FixedQ.recOn (motive := fun _ => Bool) b
        (fun _ => Bool.false)
        (fun n2 => natEqB n1 n2))

def FixedQ.ltB (a b : FixedQ) : Bool :=
  FixedQ.recOn (motive := fun _ => Bool) a
    (fun n1 =>
      FixedQ.recOn (motive := fun _ => Bool) b
        (fun n2 => natLtB n1 n2)
        (fun _ => Bool.false))
    (fun n1 =>
      FixedQ.recOn (motive := fun _ => Bool) b
        (fun _ => Bool.true)
        (fun n2 => natLtB n2 n1))

def FixedQ.leB' (a b : FixedQ) : Bool := bOr (FixedQ.ltB a b) (FixedQ.eqB a b)

def FixedQ.add (a b : FixedQ) : FixedQ :=
  FixedQ.recOn (motive := fun _ => FixedQ) a
    (fun n1 =>
      FixedQ.recOn (motive := fun _ => FixedQ) b
        (fun n2 => FixedQ.nonneg (Nat.add n1 n2))
        (fun n2 =>
          bIte (natLtB n2 n1)
            (FixedQ.nonneg (natSub n1 (Nat.succ n2)))
            (FixedQ.negsucc (natSub n2 n1))))
    (fun n1 =>
      FixedQ.recOn (motive := fun _ => FixedQ) b
        (fun n2 =>
          bIte (natLtB n1 n2)
            (FixedQ.nonneg (natSub n2 (Nat.succ n1)))
            (FixedQ.negsucc (natSub n1 n2)))
        (fun n2 => FixedQ.negsucc (Nat.succ (Nat.add n1 n2))))

def FixedQ.sub (a b : FixedQ) : FixedQ := FixedQ.add a (FixedQ.neg b)

def FixedQ.mul (a b : FixedQ) : FixedQ :=
  FixedQ.recOn (motive := fun _ => FixedQ) a
    (fun n1 =>
      FixedQ.recOn (motive := fun _ => FixedQ) b
        (fun n2 => FixedQ.nonneg (Nat.mul n1 n2))
        (fun n2 => FixedQ.neg (FixedQ.nonneg (Nat.mul n1 (Nat.succ n2)))))
    (fun n1 =>
      FixedQ.recOn (motive := fun _ => FixedQ) b
        (fun n2 => FixedQ.neg (FixedQ.nonneg (Nat.mul (Nat.succ n1) n2)))
        (fun n2 => FixedQ.nonneg (Nat.mul (Nat.succ n1) (Nat.succ n2))))

def FixedQ.absDiff (a b : FixedQ) : FixedQ :=
  FixedQ.recOn (motive := fun _ => FixedQ) (FixedQ.sub a b)
    (fun n => FixedQ.nonneg n)
    (fun n => FixedQ.nonneg (Nat.succ n))

theorem FixedQ.add_zero (x : FixedQ) : FixedQ.add x FixedQ.zero = x :=
  FixedQ.recOn (motive := fun y => FixedQ.add y FixedQ.zero = y) x
    (fun n => Eq.refl (FixedQ.nonneg (Nat.add n 0)))
    (fun n => Eq.refl (FixedQ.negsucc n))

theorem FixedQ.zero_add (x : FixedQ) : FixedQ.add FixedQ.zero x = x :=
  FixedQ.recOn (motive := fun y => FixedQ.add FixedQ.zero y = y) x
    (fun n => Eq.refl (FixedQ.nonneg n))
    (fun n => Eq.refl (FixedQ.negsucc n))

theorem FixedQ.eqB_refl (x : FixedQ) : FixedQ.eqB x x = Bool.true :=
  FixedQ.recOn (motive := fun y => FixedQ.eqB y y = Bool.true) x
    (fun n => natEqB_refl n)
    (fun n => natEqB_refl n)

theorem FixedQ.isFinite_always (x : FixedQ) : FixedQ.isFinite x = Bool.true := Eq.refl Bool.true

theorem FixedQ.neg_zero : FixedQ.neg FixedQ.zero = FixedQ.zero := Eq.refl FixedQ.zero

theorem FixedQ.sub_zero (x : FixedQ) : FixedQ.sub x FixedQ.zero = x :=
  Eq.trans
    (congrArg (FixedQ.add x) FixedQ.neg_zero)
    (FixedQ.add_zero x)

theorem FixedQ.mul_one (x : FixedQ) : FixedQ.mul x FixedQ.one = x :=
  FixedQ.recOn (motive := fun y => FixedQ.mul y FixedQ.one = y) x
    (fun n =>
      let lem : Nat.mul n 1 = n :=
        Nat.recOn (motive := fun m => Nat.mul m 1 = m) n
          (Eq.refl 0)
          (fun m ih => congrArg Nat.succ ih)
      congrArg FixedQ.nonneg lem)
    (fun n =>
      let lem : Nat.mul (Nat.succ n) 1 = Nat.succ n :=
        Nat.recOn (motive := fun m => Nat.mul m 1 = m) (Nat.succ n)
          (Eq.refl 0)
          (fun m ih => congrArg Nat.succ ih)
      let step1 : FixedQ.mul (FixedQ.negsucc n) FixedQ.one
                 = FixedQ.neg (FixedQ.nonneg (Nat.mul (Nat.succ n) 1)) := Eq.refl _
      let step2 : FixedQ.neg (FixedQ.nonneg (Nat.mul (Nat.succ n) 1))
                 = FixedQ.neg (FixedQ.nonneg (Nat.succ n)) :=
        congrArg (fun k => FixedQ.neg (FixedQ.nonneg k)) lem
      let step3 : FixedQ.neg (FixedQ.nonneg (Nat.succ n)) = FixedQ.negsucc n := Eq.refl _
      Eq.trans step1 (Eq.trans step2 step3))

def maxUsize : Nat := 18446744073709551615

def checkedMul (a b : Nat) : ResultT Nat :=
  bIte (natLeB (Nat.mul a b) maxUsize)
    (ResultT.ok (Nat.mul a b))
    (ResultT.err ZigError.overflow)

def checkedAdd (a b : Nat) : ResultT Nat :=
  bIte (natLeB (Nat.add a b) maxUsize)
    (ResultT.ok (Nat.add a b))
    (ResultT.err ZigError.overflow)

def checkedMulU64 (a b : Nat) : ResultT Nat := checkedMul a b
def checkedAddU64 (a b : Nat) : ResultT Nat := checkedAdd a b

def checkedCastU64ToUsize (v : Nat) : ResultT Nat :=
  bIte (natLeB v maxUsize) (ResultT.ok v) (ResultT.err ZigError.tooLarge)

theorem checkedMul_ok_of_bound (a b : Nat)
    (h : natLeB (Nat.mul a b) maxUsize = Bool.true) :
    checkedMul a b = ResultT.ok (Nat.mul a b) :=
  congrArg
    (fun c => bIte c (ResultT.ok (Nat.mul a b)) (ResultT.err ZigError.overflow))
    h

theorem checkedMul_err_of_overflow (a b : Nat)
    (h : natLeB (Nat.mul a b) maxUsize = Bool.false) :
    checkedMul a b = ResultT.err ZigError.overflow :=
  congrArg
    (fun c => bIte c (ResultT.ok (Nat.mul a b)) (ResultT.err ZigError.overflow))
    h

theorem checkedAdd_ok_of_bound (a b : Nat)
    (h : natLeB (Nat.add a b) maxUsize = Bool.true) :
    checkedAdd a b = ResultT.ok (Nat.add a b) :=
  congrArg
    (fun c => bIte c (ResultT.ok (Nat.add a b)) (ResultT.err ZigError.overflow))
    h

theorem checkedAdd_err_of_overflow (a b : Nat)
    (h : natLeB (Nat.add a b) maxUsize = Bool.false) :
    checkedAdd a b = ResultT.err ZigError.overflow :=
  congrArg
    (fun c => bIte c (ResultT.ok (Nat.add a b)) (ResultT.err ZigError.overflow))
    h

theorem checkedMul_ok_zero_right (a : Nat) : checkedMul a 0 = ResultT.ok 0 :=
  checkedMul_ok_of_bound a 0 (natLeB_zero maxUsize)

theorem checkedMul_preserves_overflow (a b : Nat)
    (h : natLeB (Nat.mul a b) maxUsize = Bool.true) :
    ResultT.isOk (checkedMul a b) = Bool.true :=
  Eq.trans (congrArg ResultT.isOk (checkedMul_ok_of_bound a b h))
           (Eq.refl Bool.true)

inductive Shape : Type where
  | mk : List Nat → Shape

def Shape.dims (s : Shape) : List Nat :=
  Shape.recOn (motive := fun _ => List Nat) s (fun l => l)

def Shape.dimsLen (s : Shape) : Nat := List.length (Shape.dims s)

def Shape.nthDim (s : Shape) (i : Nat) (fallback : Nat) : Nat :=
  let d := Shape.dims s
  Nat.recOn (motive := fun _ => List Nat → Nat) i
    (fun xs => List.recOn (motive := fun _ => Nat) xs fallback (fun h _ _ => h))
    (fun _ ih xs => List.recOn (motive := fun _ => Nat) xs fallback (fun _ t _ => ih t))
    d

def Shape.mk2D (rows cols : Nat) : Shape := Shape.mk (List.cons rows (List.cons cols List.nil))

theorem Shape.mk2D_dimsLen (rows cols : Nat) : Shape.dimsLen (Shape.mk2D rows cols) = 2 :=
  Eq.refl 2

theorem Shape.mk2D_nth0 (rows cols : Nat) (fb : Nat) :
    Shape.nthDim (Shape.mk2D rows cols) 0 fb = rows := Eq.refl rows

theorem Shape.mk2D_nth1 (rows cols : Nat) (fb : Nat) :
    Shape.nthDim (Shape.mk2D rows cols) 1 fb = cols := Eq.refl cols

inductive Tensor : Type where
  | mk : Shape → List FixedQ → Tensor

def Tensor.shape (t : Tensor) : Shape :=
  Tensor.recOn (motive := fun _ => Shape) t (fun s _ => s)

def Tensor.data (t : Tensor) : List FixedQ :=
  Tensor.recOn (motive := fun _ => List FixedQ) t (fun _ d => d)

def Tensor.dims (t : Tensor) : List Nat := Shape.dims (Tensor.shape t)
def Tensor.dimsLen (t : Tensor) : Nat := List.length (Tensor.dims t)
def Tensor.dataLen (t : Tensor) : Nat := List.length (Tensor.data t)

def Tensor.rows2D (t : Tensor) : Nat := Shape.nthDim (Tensor.shape t) 0 0
def Tensor.cols2D (t : Tensor) : Nat := Shape.nthDim (Tensor.shape t) 1 0

def Tensor.wellFormed2D (t : Tensor) : Prop :=
  Tensor.dataLen t = Nat.mul (Tensor.rows2D t) (Tensor.cols2D t)

def Tensor.initZeros2D (rows cols : Nat) : Tensor :=
  Tensor.mk (Shape.mk2D rows cols) (List.replicate (Nat.mul rows cols) FixedQ.zero)

theorem Tensor.initZeros2D_shape (rows cols : Nat) :
    Tensor.shape (Tensor.initZeros2D rows cols) = Shape.mk2D rows cols :=
  Eq.refl _

theorem Tensor.initZeros2D_dataLen (rows cols : Nat) :
    Tensor.dataLen (Tensor.initZeros2D rows cols) = Nat.mul rows cols :=
  List.length_replicate (Nat.mul rows cols) FixedQ.zero

theorem Tensor.initZeros2D_rows (rows cols : Nat) :
    Tensor.rows2D (Tensor.initZeros2D rows cols) = rows := Eq.refl rows

theorem Tensor.initZeros2D_cols (rows cols : Nat) :
    Tensor.cols2D (Tensor.initZeros2D rows cols) = cols := Eq.refl cols

theorem Tensor.initZeros2D_wellFormed (rows cols : Nat) :
    Tensor.wellFormed2D (Tensor.initZeros2D rows cols) :=
  List.length_replicate (Nat.mul rows cols) FixedQ.zero

def Tensor.initFromData2D (rows cols : Nat) (d : List FixedQ) : Tensor :=
  Tensor.mk (Shape.mk2D rows cols) d

theorem Tensor.initFromData2D_shape (rows cols : Nat) (d : List FixedQ) :
    Tensor.shape (Tensor.initFromData2D rows cols d) = Shape.mk2D rows cols :=
  Eq.refl _

theorem Tensor.initFromData2D_rows (rows cols : Nat) (d : List FixedQ) :
    Tensor.rows2D (Tensor.initFromData2D rows cols d) = rows := Eq.refl rows

theorem Tensor.initFromData2D_cols (rows cols : Nat) (d : List FixedQ) :
    Tensor.cols2D (Tensor.initFromData2D rows cols d) = cols := Eq.refl cols

theorem Tensor.initFromData2D_data (rows cols : Nat) (d : List FixedQ) :
    Tensor.data (Tensor.initFromData2D rows cols d) = d := Eq.refl _

theorem Tensor.initFromData2D_dimsLen (rows cols : Nat) (d : List FixedQ) :
    Tensor.dimsLen (Tensor.initFromData2D rows cols d) = 2 := Eq.refl 2

def Tensor.hasShape2D (t : Tensor) (rows cols : Nat) : Bool :=
  bAnd (natEqB (Tensor.dimsLen t) 2)
    (bAnd (natEqB (Tensor.rows2D t) rows) (natEqB (Tensor.cols2D t) cols))

theorem Tensor.hasShape2D_initZeros (rows cols : Nat) :
    Tensor.hasShape2D (Tensor.initZeros2D rows cols) rows cols = Bool.true :=
  let h_rows := natEqB_refl rows
  let h_cols := natEqB_refl cols
  let step1 : bAnd (natEqB rows rows) (natEqB cols cols) = bAnd Bool.true Bool.true :=
    Eq.trans
      (congrArg (fun x => bAnd x (natEqB cols cols)) h_rows)
      (congrArg (fun x => bAnd Bool.true x) h_cols)
  Eq.trans step1 (Eq.refl Bool.true)

def Tensor.sameShape (a b : Tensor) : Bool :=
  bAnd (natEqB (Tensor.dimsLen a) 2)
    (bAnd (natEqB (Tensor.dimsLen b) 2)
      (bAnd (natEqB (Tensor.rows2D a) (Tensor.rows2D b))
            (natEqB (Tensor.cols2D a) (Tensor.cols2D b))))

theorem Tensor.sameShape_refl_2D (rows cols : Nat) :
    Tensor.sameShape (Tensor.initZeros2D rows cols) (Tensor.initZeros2D rows cols) = Bool.true :=
  let t := Tensor.initZeros2D rows cols
  let h_rows := natEqB_refl (Tensor.rows2D t)
  let h_cols := natEqB_refl (Tensor.cols2D t)
  let step_inner : bAnd (natEqB (Tensor.rows2D t) (Tensor.rows2D t))
                        (natEqB (Tensor.cols2D t) (Tensor.cols2D t)) = Bool.true :=
    Eq.trans
      (congrArg (fun x => bAnd x (natEqB (Tensor.cols2D t) (Tensor.cols2D t))) h_rows)
      (Eq.trans
        (congrArg (fun x => bAnd Bool.true x) h_cols)
        (Eq.refl Bool.true))
  Eq.trans
    (congrArg (fun x => bAnd (natEqB (Tensor.dimsLen t) 2)
                             (bAnd (natEqB (Tensor.dimsLen t) 2) x)) step_inner)
    (Eq.refl Bool.true)

theorem Tensor.sameShape_refl (t : Tensor)
    (hd : Tensor.dimsLen t = 2) : Tensor.sameShape t t = Bool.true :=
  let hdB : natEqB (Tensor.dimsLen t) 2 = Bool.true :=
    Eq.trans (congrArg (fun n => natEqB n 2) hd) (natEqB_refl 2)
  let hRows : natEqB (Tensor.rows2D t) (Tensor.rows2D t) = Bool.true := natEqB_refl _
  let hCols : natEqB (Tensor.cols2D t) (Tensor.cols2D t) = Bool.true := natEqB_refl _
  let inner : bAnd (natEqB (Tensor.rows2D t) (Tensor.rows2D t))
                   (natEqB (Tensor.cols2D t) (Tensor.cols2D t)) = Bool.true :=
    Eq.trans (congrArg (fun x => bAnd x (natEqB (Tensor.cols2D t) (Tensor.cols2D t))) hRows)
      (Eq.trans (congrArg (fun x => bAnd Bool.true x) hCols) (Eq.refl Bool.true))
  let outer : bAnd (natEqB (Tensor.dimsLen t) 2)
                   (bAnd (natEqB (Tensor.rows2D t) (Tensor.rows2D t))
                         (natEqB (Tensor.cols2D t) (Tensor.cols2D t))) = Bool.true :=
    Eq.trans (congrArg (fun x => bAnd (natEqB (Tensor.dimsLen t) 2) x) inner)
      (Eq.trans (congrArg (fun x => bAnd x Bool.true) hdB) (Eq.refl Bool.true))
  Eq.trans (congrArg (fun x => bAnd (natEqB (Tensor.dimsLen t) 2)
                                   (bAnd x (bAnd (natEqB (Tensor.rows2D t) (Tensor.rows2D t))
                                                 (natEqB (Tensor.cols2D t) (Tensor.cols2D t))))) hdB)
    (Eq.trans (congrArg (fun x => bAnd (natEqB (Tensor.dimsLen t) 2)
                                      (bAnd Bool.true x)) inner)
      (Eq.trans (congrArg (fun x => bAnd x Bool.true) hdB)
        (Eq.refl Bool.true)))

def validateTensor2D (t : Tensor) : ResultT Nat :=
  bIte (natEqB (Tensor.dimsLen t) 2)
    (ResultT.bind (checkedMul (Tensor.rows2D t) (Tensor.cols2D t))
      (fun expected =>
        bIte (natEqB (Tensor.dataLen t) expected)
          (ResultT.ok expected)
          (ResultT.err ZigError.dataLengthMismatch)))
    (ResultT.err ZigError.shapeMismatch)

def validateTensor2DShape (t : Tensor) (rows cols : Nat) : ResultT Nat :=
  bIte (bAnd (natEqB (Tensor.dimsLen t) 2)
             (bAnd (natEqB (Tensor.rows2D t) rows)
                   (natEqB (Tensor.cols2D t) cols)))
    (ResultT.bind (checkedMul rows cols)
      (fun expected =>
        bIte (natEqB (Tensor.dataLen t) expected)
          (ResultT.ok expected)
          (ResultT.err ZigError.dataLengthMismatch)))
    (ResultT.err ZigError.shapeMismatch)

theorem validateTensor2D_initZeros_ok (rows cols : Nat)
    (hbound : natLeB (Nat.mul rows cols) maxUsize = Bool.true) :
    validateTensor2D (Tensor.initZeros2D rows cols) = ResultT.ok (Nat.mul rows cols) :=
  let t := Tensor.initZeros2D rows cols
  let h_checked : checkedMul rows cols = ResultT.ok (Nat.mul rows cols) :=
    checkedMul_ok_of_bound rows cols hbound
  let h_dataLen : Tensor.dataLen t = Nat.mul rows cols :=
    List.length_replicate (Nat.mul rows cols) FixedQ.zero
  let h_eqDataLen : natEqB (Tensor.dataLen t) (Nat.mul rows cols) = Bool.true :=
    Eq.trans (congrArg (fun x => natEqB x (Nat.mul rows cols)) h_dataLen)
             (natEqB_refl (Nat.mul rows cols))
  let innerBind :=
    ResultT.bind (checkedMul rows cols)
      (fun expected =>
        bIte (natEqB (Tensor.dataLen t) expected)
          (ResultT.ok expected)
          (ResultT.err ZigError.dataLengthMismatch))
  let step1 : innerBind
    = ResultT.bind (ResultT.ok (Nat.mul rows cols))
      (fun expected =>
        bIte (natEqB (Tensor.dataLen t) expected)
          (ResultT.ok expected)
          (ResultT.err ZigError.dataLengthMismatch)) :=
    congrArg (fun r => ResultT.bind r
      (fun expected =>
        bIte (natEqB (Tensor.dataLen t) expected)
          (ResultT.ok expected)
          (ResultT.err ZigError.dataLengthMismatch))) h_checked
  let step2 : ResultT.bind (ResultT.ok (Nat.mul rows cols))
      (fun expected =>
        bIte (natEqB (Tensor.dataLen t) expected)
          (ResultT.ok expected)
          (ResultT.err ZigError.dataLengthMismatch))
    = bIte (natEqB (Tensor.dataLen t) (Nat.mul rows cols))
        (ResultT.ok (Nat.mul rows cols))
        (ResultT.err ZigError.dataLengthMismatch) :=
    ResultT.bind_ok_eq (Nat.mul rows cols)
      (fun expected =>
        bIte (natEqB (Tensor.dataLen t) expected)
          (ResultT.ok expected)
          (ResultT.err ZigError.dataLengthMismatch))
  let step3 : bIte (natEqB (Tensor.dataLen t) (Nat.mul rows cols))
        (ResultT.ok (Nat.mul rows cols))
        (ResultT.err ZigError.dataLengthMismatch)
    = ResultT.ok (Nat.mul rows cols) :=
    congrArg (fun c => bIte c (ResultT.ok (Nat.mul rows cols))
                              (ResultT.err ZigError.dataLengthMismatch)) h_eqDataLen
  Eq.trans step1 (Eq.trans step2 step3)

theorem validateTensor2D_ok_dims (t : Tensor) (n : Nat)
    (h : validateTensor2D t = ResultT.ok n) :
    natEqB (Tensor.dimsLen t) 2 = Bool.true :=
  Bool.recOn
    (motive := fun bv =>
      bv = natEqB (Tensor.dimsLen t) 2 →
      bIte bv
        (ResultT.bind (checkedMul (Tensor.rows2D t) (Tensor.cols2D t))
          (fun expected =>
            bIte (natEqB (Tensor.dataLen t) expected)
              (ResultT.ok expected)
              (ResultT.err ZigError.dataLengthMismatch)))
        (ResultT.err ZigError.shapeMismatch)
      = ResultT.ok n →
      natEqB (Tensor.dimsLen t) 2 = Bool.true)
    (fun _ hv =>
      False.elim (ResultT.noConfusion hv (fun _ => False.elim (boolFalseNeTrue (Eq.refl _)))))
    (fun heq _ => Eq.symm heq)
    (natEqB (Tensor.dimsLen t) 2) (Eq.refl _) h

def validateClipRange (cmin cmax : FixedQ) : ResultT Unit :=
  bIte (bNot (bAnd (FixedQ.isFinite cmin) (FixedQ.isFinite cmax)))
    (ResultT.err ZigError.nonFinite)
    (bIte (bNot (FixedQ.ltB cmin cmax))
      (ResultT.err ZigError.invalidConfig)
      (bIte (bOr (FixedQ.ltB (FixedQ.nonneg 20) cmax)
                 (FixedQ.ltB cmin (FixedQ.negsucc 19)))
        (ResultT.err ZigError.invalidConfig)
        (ResultT.ok Unit.unit)))

theorem validateClipRange_finite_always (cmin cmax : FixedQ) :
    bNot (bAnd (FixedQ.isFinite cmin) (FixedQ.isFinite cmax)) = Bool.false :=
  let h1 : FixedQ.isFinite cmin = Bool.true := Eq.refl Bool.true
  let h2 : FixedQ.isFinite cmax = Bool.true := Eq.refl Bool.true
  let step : bAnd (FixedQ.isFinite cmin) (FixedQ.isFinite cmax) = Bool.true :=
    Eq.trans (congrArg (fun x => bAnd x (FixedQ.isFinite cmax)) h1)
             (Eq.trans (congrArg (fun x => bAnd Bool.true x) h2) (Eq.refl Bool.true))
  Eq.trans (congrArg bNot step) (Eq.refl Bool.false)

theorem validateClipRange_implies_ordered (cmin cmax : FixedQ)
    (h : validateClipRange cmin cmax = ResultT.ok Unit.unit) :
    FixedQ.ltB cmin cmax = Bool.true :=
  let finiteStep :
      validateClipRange cmin cmax
      = bIte (bNot (FixedQ.ltB cmin cmax))
          (ResultT.err ZigError.invalidConfig)
          (bIte (bOr (FixedQ.ltB (FixedQ.nonneg 20) cmax)
                     (FixedQ.ltB cmin (FixedQ.negsucc 19)))
            (ResultT.err ZigError.invalidConfig)
            (ResultT.ok Unit.unit)) :=
    congrArg (fun c => bIte c (ResultT.err ZigError.nonFinite)
                             (bIte (bNot (FixedQ.ltB cmin cmax))
                                (ResultT.err ZigError.invalidConfig)
                                (bIte (bOr (FixedQ.ltB (FixedQ.nonneg 20) cmax)
                                           (FixedQ.ltB cmin (FixedQ.negsucc 19)))
                                  (ResultT.err ZigError.invalidConfig)
                                  (ResultT.ok Unit.unit))))
             (validateClipRange_finite_always cmin cmax)
  let h' :
      bIte (bNot (FixedQ.ltB cmin cmax))
        (ResultT.err ZigError.invalidConfig)
        (bIte (bOr (FixedQ.ltB (FixedQ.nonneg 20) cmax)
                   (FixedQ.ltB cmin (FixedQ.negsucc 19)))
          (ResultT.err ZigError.invalidConfig)
          (ResultT.ok Unit.unit))
      = ResultT.ok Unit.unit :=
    Eq.trans (Eq.symm finiteStep) h
  Bool.recOn
    (motive := fun bv =>
      FixedQ.ltB cmin cmax = bv →
      bIte (bNot bv)
        (ResultT.err ZigError.invalidConfig)
        (bIte (bOr (FixedQ.ltB (FixedQ.nonneg 20) cmax)
                   (FixedQ.ltB cmin (FixedQ.negsucc 19)))
          (ResultT.err ZigError.invalidConfig)
          (ResultT.ok Unit.unit))
      = ResultT.ok Unit.unit →
      FixedQ.ltB cmin cmax = Bool.true)
    (fun _ hk =>
      False.elim (ResultT.noConfusion hk (fun _ => False.elim (boolFalseNeTrue (Eq.refl _)))))
    (fun heq _ => heq)
    (FixedQ.ltB cmin cmax) (Eq.refl _) h'

def validateComparisonTolerances (absTol relTol : FixedQ) : ResultT Unit :=
  bIte (bNot (bAnd (FixedQ.isFinite absTol) (FixedQ.isFinite relTol)))
    (ResultT.err ZigError.invalidTolerance)
    (bIte (bOr (FixedQ.ltB absTol FixedQ.zero) (FixedQ.ltB relTol FixedQ.zero))
      (ResultT.err ZigError.invalidTolerance)
      (ResultT.ok Unit.unit))

theorem validateComparisonTolerances_finite_always (absTol relTol : FixedQ) :
    bNot (bAnd (FixedQ.isFinite absTol) (FixedQ.isFinite relTol)) = Bool.false :=
  let h1 : FixedQ.isFinite absTol = Bool.true := Eq.refl Bool.true
  let h2 : FixedQ.isFinite relTol = Bool.true := Eq.refl Bool.true
  let step : bAnd (FixedQ.isFinite absTol) (FixedQ.isFinite relTol) = Bool.true :=
    Eq.trans (congrArg (fun x => bAnd x (FixedQ.isFinite relTol)) h1)
             (Eq.trans (congrArg (fun x => bAnd Bool.true x) h2) (Eq.refl Bool.true))
  Eq.trans (congrArg bNot step) (Eq.refl Bool.false)

theorem validateComparisonTolerances_ok_implies_nonneg
    (absTol relTol : FixedQ)
    (h : validateComparisonTolerances absTol relTol = ResultT.ok Unit.unit) :
    And (FixedQ.ltB absTol FixedQ.zero = Bool.false)
        (FixedQ.ltB relTol FixedQ.zero = Bool.false) :=
  let finiteStep :
      validateComparisonTolerances absTol relTol
      = bIte (bOr (FixedQ.ltB absTol FixedQ.zero) (FixedQ.ltB relTol FixedQ.zero))
          (ResultT.err ZigError.invalidTolerance)
          (ResultT.ok Unit.unit) :=
    congrArg (fun c => bIte c
        (ResultT.err ZigError.invalidTolerance)
        (bIte (bOr (FixedQ.ltB absTol FixedQ.zero) (FixedQ.ltB relTol FixedQ.zero))
          (ResultT.err ZigError.invalidTolerance)
          (ResultT.ok Unit.unit)))
      (validateComparisonTolerances_finite_always absTol relTol)
  let h' :
      bIte (bOr (FixedQ.ltB absTol FixedQ.zero) (FixedQ.ltB relTol FixedQ.zero))
        (ResultT.err ZigError.invalidTolerance)
        (ResultT.ok Unit.unit)
      = ResultT.ok Unit.unit :=
    Eq.trans (Eq.symm finiteStep) h
  Bool.recOn
    (motive := fun bv =>
      bOr (FixedQ.ltB absTol FixedQ.zero) (FixedQ.ltB relTol FixedQ.zero) = bv →
      bIte bv (ResultT.err ZigError.invalidTolerance) (ResultT.ok Unit.unit)
      = ResultT.ok Unit.unit →
      And (FixedQ.ltB absTol FixedQ.zero = Bool.false)
          (FixedQ.ltB relTol FixedQ.zero = Bool.false))
    (fun hOrFalse _ =>
      Bool.recOn
        (motive := fun ba =>
          FixedQ.ltB absTol FixedQ.zero = ba →
          bOr ba (FixedQ.ltB relTol FixedQ.zero) = Bool.false →
          And (FixedQ.ltB absTol FixedQ.zero = Bool.false)
              (FixedQ.ltB relTol FixedQ.zero = Bool.false))
        (FixedQ.ltB absTol FixedQ.zero)
        (fun heqa horFalse =>
          Bool.recOn
            (motive := fun br =>
              FixedQ.ltB relTol FixedQ.zero = br →
              bOr Bool.false br = Bool.false →
              And (FixedQ.ltB absTol FixedQ.zero = Bool.false)
                  (FixedQ.ltB relTol FixedQ.zero = Bool.false))
            (FixedQ.ltB relTol FixedQ.zero)
            (fun heqr _ => And.intro heqa heqr)
            (fun heqr hkf => False.elim (boolTrueNeFalse (Eq.trans (Eq.symm (bOr_false_l Bool.true)) hkf)))
            (Eq.refl _) horFalse)
        (fun heqa horFalse =>
          False.elim (boolTrueNeFalse
            (Eq.trans (Eq.symm (bOr_true_l (FixedQ.ltB relTol FixedQ.zero))) horFalse)))
        (Eq.refl _)
        (Eq.trans (congrArg (fun x => bOr x (FixedQ.ltB relTol FixedQ.zero)) (Eq.refl _)) hOrFalse))
    (fun _ hk =>
      False.elim (ResultT.noConfusion hk (fun _ => False.elim (boolFalseNeTrue (Eq.refl _)))))
    (bOr (FixedQ.ltB absTol FixedQ.zero) (FixedQ.ltB relTol FixedQ.zero))
    (Eq.refl _) h'

inductive TensorAddr : Type where
  | mk : Nat → TensorAddr

def TensorAddr.base (a : TensorAddr) : Nat :=
  TensorAddr.recOn (motive := fun _ => Nat) a (fun b => b)

inductive AddrTensor : Type where
  | mk : Tensor → TensorAddr → AddrTensor

def AddrTensor.tensor (a : AddrTensor) : Tensor :=
  AddrTensor.recOn (motive := fun _ => Tensor) a (fun t _ => t)

def AddrTensor.addr (a : AddrTensor) : TensorAddr :=
  AddrTensor.recOn (motive := fun _ => TensorAddr) a (fun _ addr => addr)

def tensorBytes (a : AddrTensor) : Nat :=
  Nat.mul (Tensor.dataLen (AddrTensor.tensor a)) 4

def tensorStart (a : AddrTensor) : Nat :=
  TensorAddr.base (AddrTensor.addr a)

def tensorEnd (a : AddrTensor) : Nat :=
  Nat.add (tensorStart a) (tensorBytes a)

def tensorsOverlap (a b : AddrTensor) : Bool :=
  bIte (bOr (natEqB (Tensor.dataLen (AddrTensor.tensor a)) 0)
            (natEqB (Tensor.dataLen (AddrTensor.tensor b)) 0))
    Bool.false
    (bAnd (natLtB (tensorStart a) (tensorEnd b))
          (natLtB (tensorStart b) (tensorEnd a)))

theorem tensorsOverlap_symm (a b : AddrTensor) :
    tensorsOverlap a b = tensorsOverlap b a :=
  let outerEq :
      bOr (natEqB (Tensor.dataLen (AddrTensor.tensor a)) 0)
          (natEqB (Tensor.dataLen (AddrTensor.tensor b)) 0)
      = bOr (natEqB (Tensor.dataLen (AddrTensor.tensor b)) 0)
            (natEqB (Tensor.dataLen (AddrTensor.tensor a)) 0) :=
    bOr_comm _ _
  let innerEq :
      bAnd (natLtB (tensorStart a) (tensorEnd b))
           (natLtB (tensorStart b) (tensorEnd a))
      = bAnd (natLtB (tensorStart b) (tensorEnd a))
             (natLtB (tensorStart a) (tensorEnd b)) :=
    bAnd_comm _ _
  Eq.trans (congrArg
    (fun c => bIte c Bool.false
                   (bAnd (natLtB (tensorStart a) (tensorEnd b))
                         (natLtB (tensorStart b) (tensorEnd a))))
    outerEq)
    (congrArg
      (fun c => bIte (bOr (natEqB (Tensor.dataLen (AddrTensor.tensor b)) 0)
                          (natEqB (Tensor.dataLen (AddrTensor.tensor a)) 0))
                     Bool.false c)
      innerEq)

def sameTensorStorage (a b : AddrTensor) : Bool :=
  bAnd (natEqB (Tensor.dataLen (AddrTensor.tensor a))
               (Tensor.dataLen (AddrTensor.tensor b)))
       (bOr (natEqB (Tensor.dataLen (AddrTensor.tensor a)) 0)
            (natEqB (tensorStart a) (tensorStart b)))

theorem sameTensorStorage_refl (a : AddrTensor) :
    sameTensorStorage a a = Bool.true :=
  let eqLen : natEqB (Tensor.dataLen (AddrTensor.tensor a))
                     (Tensor.dataLen (AddrTensor.tensor a)) = Bool.true :=
    natEqB_refl _
  let eqStart : natEqB (tensorStart a) (tensorStart a) = Bool.true :=
    natEqB_refl _
  let orStep : bOr (natEqB (Tensor.dataLen (AddrTensor.tensor a)) 0)
                   (natEqB (tensorStart a) (tensorStart a)) = Bool.true :=
    Eq.trans (congrArg (fun x => bOr (natEqB (Tensor.dataLen (AddrTensor.tensor a)) 0) x)
                       eqStart)
             (bOr_true_r _)
  Eq.trans (congrArg (fun x => bAnd x (bOr (natEqB (Tensor.dataLen (AddrTensor.tensor a)) 0)
                                           (natEqB (tensorStart a) (tensorStart a)))) eqLen)
           (Eq.trans (congrArg (fun x => bAnd Bool.true x) orStep)
                     (Eq.refl Bool.true))

def copyTensorPairInto (out1 out2 in1 in2 : AddrTensor) : ResultT Unit :=
  bIte (tensorsOverlap out1 out2)
    (ResultT.err ZigError.aliasedBuffers)
    (ResultT.ok Unit.unit)

theorem copyTensorPairInto_noAlias (a b : AddrTensor)
    (h : tensorsOverlap a b = Bool.false) :
    copyTensorPairInto a b a b = ResultT.ok Unit.unit :=
  congrArg (fun c => bIte c (ResultT.err ZigError.aliasedBuffers) (ResultT.ok Unit.unit)) h

inductive RSFLayerConfig : Type where
  | mk : FixedQ → FixedQ → Nat → Bool → RSFLayerConfig

def RSFLayerConfig.clipMin (c : RSFLayerConfig) : FixedQ :=
  RSFLayerConfig.recOn (motive := fun _ => FixedQ) c (fun cmin _ _ _ => cmin)
def RSFLayerConfig.clipMax (c : RSFLayerConfig) : FixedQ :=
  RSFLayerConfig.recOn (motive := fun _ => FixedQ) c (fun _ cmax _ _ => cmax)
def RSFLayerConfig.seedOffset (c : RSFLayerConfig) : Nat :=
  RSFLayerConfig.recOn (motive := fun _ => Nat) c (fun _ _ s _ => s)
def RSFLayerConfig.gradMean (c : RSFLayerConfig) : Bool :=
  RSFLayerConfig.recOn (motive := fun _ => Bool) c (fun _ _ _ g => g)

def RSFLayerConfig.default : RSFLayerConfig :=
  RSFLayerConfig.mk (FixedQ.negsucc 4) (FixedQ.nonneg 5) 0 Bool.true

inductive RSFConfig : Type where
  | mk : FixedQ → FixedQ → Bool → Nat → Nat → RSFConfig

def RSFConfig.clipMin (c : RSFConfig) : FixedQ :=
  RSFConfig.recOn (motive := fun _ => FixedQ) c (fun cmin _ _ _ _ => cmin)
def RSFConfig.clipMax (c : RSFConfig) : FixedQ :=
  RSFConfig.recOn (motive := fun _ => FixedQ) c (fun _ cmax _ _ _ => cmax)
def RSFConfig.gradMean (c : RSFConfig) : Bool :=
  RSFConfig.recOn (motive := fun _ => Bool) c (fun _ _ g _ _ => g)
def RSFConfig.maxDim (c : RSFConfig) : Nat :=
  RSFConfig.recOn (motive := fun _ => Nat) c (fun _ _ _ md _ => md)
def RSFConfig.maxLayers (c : RSFConfig) : Nat :=
  RSFConfig.recOn (motive := fun _ => Nat) c (fun _ _ _ _ ml => ml)

def RSFConfig.default : RSFConfig :=
  RSFConfig.mk (FixedQ.negsucc 4) (FixedQ.nonneg 5) Bool.true 1048576 1048576

def validateModelConfigValues (dim numLayers : Nat) (cfg : RSFConfig) : ResultT Unit :=
  bIte (natEqB dim 0)
    (ResultT.err ZigError.invalidDimension)
    (bIte (natEqB numLayers 0)
      (ResultT.err ZigError.invalidLayerCount)
      (ResultT.bind (validateClipRange (RSFConfig.clipMin cfg) (RSFConfig.clipMax cfg))
        (fun _ =>
          bIte (bOr (natEqB (RSFConfig.maxDim cfg) 0)
                    (natEqB (RSFConfig.maxLayers cfg) 0))
            (ResultT.err ZigError.invalidConfig)
            (bIte (bOr (natLtB (RSFConfig.maxDim cfg) dim)
                       (natLtB (RSFConfig.maxLayers cfg) numLayers))
              (ResultT.err ZigError.invalidConfig)
              (ResultT.ok Unit.unit)))))

theorem validateModelConfigValues_ok_dim_pos (dim numLayers : Nat) (cfg : RSFConfig)
    (h : validateModelConfigValues dim numLayers cfg = ResultT.ok Unit.unit) :
    natEqB dim 0 = Bool.false :=
  Bool.recOn
    (motive := fun bv =>
      natEqB dim 0 = bv →
      bIte bv (ResultT.err ZigError.invalidDimension)
        (bIte (natEqB numLayers 0)
          (ResultT.err ZigError.invalidLayerCount)
          (ResultT.bind (validateClipRange (RSFConfig.clipMin cfg) (RSFConfig.clipMax cfg))
            (fun _ =>
              bIte (bOr (natEqB (RSFConfig.maxDim cfg) 0)
                        (natEqB (RSFConfig.maxLayers cfg) 0))
                (ResultT.err ZigError.invalidConfig)
                (bIte (bOr (natLtB (RSFConfig.maxDim cfg) dim)
                           (natLtB (RSFConfig.maxLayers cfg) numLayers))
                  (ResultT.err ZigError.invalidConfig)
                  (ResultT.ok Unit.unit)))))
      = ResultT.ok Unit.unit →
      natEqB dim 0 = Bool.false)
    (fun heq _ => heq)
    (fun _ hv => False.elim (ResultT.noConfusion hv (fun _ =>
                   False.elim (boolFalseNeTrue (Eq.refl _)))))
    (natEqB dim 0) (Eq.refl _) h

theorem validateModelConfigValues_ok_layers_pos (dim numLayers : Nat) (cfg : RSFConfig)
    (h : validateModelConfigValues dim numLayers cfg = ResultT.ok Unit.unit) :
    natEqB numLayers 0 = Bool.false :=
  let hdim : natEqB dim 0 = Bool.false :=
    validateModelConfigValues_ok_dim_pos dim numLayers cfg h
  let afterDim :
      validateModelConfigValues dim numLayers cfg
      = bIte (natEqB numLayers 0)
          (ResultT.err ZigError.invalidLayerCount)
          (ResultT.bind (validateClipRange (RSFConfig.clipMin cfg) (RSFConfig.clipMax cfg))
            (fun _ =>
              bIte (bOr (natEqB (RSFConfig.maxDim cfg) 0)
                        (natEqB (RSFConfig.maxLayers cfg) 0))
                (ResultT.err ZigError.invalidConfig)
                (bIte (bOr (natLtB (RSFConfig.maxDim cfg) dim)
                           (natLtB (RSFConfig.maxLayers cfg) numLayers))
                  (ResultT.err ZigError.invalidConfig)
                  (ResultT.ok Unit.unit)))) :=
    congrArg (fun c => bIte c (ResultT.err ZigError.invalidDimension)
      (bIte (natEqB numLayers 0)
        (ResultT.err ZigError.invalidLayerCount)
        (ResultT.bind (validateClipRange (RSFConfig.clipMin cfg) (RSFConfig.clipMax cfg))
          (fun _ =>
            bIte (bOr (natEqB (RSFConfig.maxDim cfg) 0)
                      (natEqB (RSFConfig.maxLayers cfg) 0))
              (ResultT.err ZigError.invalidConfig)
              (bIte (bOr (natLtB (RSFConfig.maxDim cfg) dim)
                         (natLtB (RSFConfig.maxLayers cfg) numLayers))
                (ResultT.err ZigError.invalidConfig)
                (ResultT.ok Unit.unit)))))) hdim
  let h' := Eq.trans (Eq.symm afterDim) h
  Bool.recOn
    (motive := fun bv =>
      natEqB numLayers 0 = bv →
      bIte bv (ResultT.err ZigError.invalidLayerCount)
        (ResultT.bind (validateClipRange (RSFConfig.clipMin cfg) (RSFConfig.clipMax cfg))
          (fun _ =>
            bIte (bOr (natEqB (RSFConfig.maxDim cfg) 0)
                      (natEqB (RSFConfig.maxLayers cfg) 0))
              (ResultT.err ZigError.invalidConfig)
              (bIte (bOr (natLtB (RSFConfig.maxDim cfg) dim)
                         (natLtB (RSFConfig.maxLayers cfg) numLayers))
                (ResultT.err ZigError.invalidConfig)
                (ResultT.ok Unit.unit))))
      = ResultT.ok Unit.unit →
      natEqB numLayers 0 = Bool.false)
    (fun heq _ => heq)
    (fun _ hv => False.elim (ResultT.noConfusion hv (fun _ =>
                   False.elim (boolFalseNeTrue (Eq.refl _)))))
    (natEqB numLayers 0) (Eq.refl _) h'

inductive LayerCore : Type where
  | mk :
      (sWeight tWeight sBias tBias : Tensor) →
      (dim : Nat) →
      (clipMin clipMax : FixedQ) →
      (gradMean : Bool) →
      LayerCore

def LayerCore.sWeight (l : LayerCore) : Tensor :=
  LayerCore.recOn (motive := fun _ => Tensor) l
    (fun sw _ _ _ _ _ _ _ => sw)
def LayerCore.tWeight (l : LayerCore) : Tensor :=
  LayerCore.recOn (motive := fun _ => Tensor) l
    (fun _ tw _ _ _ _ _ _ => tw)
def LayerCore.sBias (l : LayerCore) : Tensor :=
  LayerCore.recOn (motive := fun _ => Tensor) l
    (fun _ _ sb _ _ _ _ _ => sb)
def LayerCore.tBias (l : LayerCore) : Tensor :=
  LayerCore.recOn (motive := fun _ => Tensor) l
    (fun _ _ _ tb _ _ _ _ => tb)
def LayerCore.dim (l : LayerCore) : Nat :=
  LayerCore.recOn (motive := fun _ => Nat) l
    (fun _ _ _ _ d _ _ _ => d)
def LayerCore.clipMin (l : LayerCore) : FixedQ :=
  LayerCore.recOn (motive := fun _ => FixedQ) l
    (fun _ _ _ _ _ cmin _ _ => cmin)
def LayerCore.clipMax (l : LayerCore) : FixedQ :=
  LayerCore.recOn (motive := fun _ => FixedQ) l
    (fun _ _ _ _ _ _ cmax _ => cmax)
def LayerCore.gradMean (l : LayerCore) : Bool :=
  LayerCore.recOn (motive := fun _ => Bool) l
    (fun _ _ _ _ _ _ _ g => g)

def LayerCore.initOwned (dim : Nat) (cfg : RSFLayerConfig) : ResultT LayerCore :=
  bIte (natEqB dim 0)
    (ResultT.err ZigError.invalidDimension)
    (ResultT.bind (validateClipRange (RSFLayerConfig.clipMin cfg) (RSFLayerConfig.clipMax cfg))
      (fun _ =>
        ResultT.bind (checkedMul dim dim)
          (fun _ =>
            ResultT.ok
              (LayerCore.mk
                (Tensor.initZeros2D dim dim)
                (Tensor.initZeros2D dim dim)
                (Tensor.initZeros2D 1 dim)
                (Tensor.initZeros2D 1 dim)
                dim
                (RSFLayerConfig.clipMin cfg)
                (RSFLayerConfig.clipMax cfg)
                (RSFLayerConfig.gradMean cfg)))))

theorem LayerCore.initOwned_ok_implies_dim_pos (dim : Nat) (cfg : RSFLayerConfig) (l : LayerCore)
    (h : LayerCore.initOwned dim cfg = ResultT.ok l) :
    natEqB dim 0 = Bool.false :=
  Bool.recOn
    (motive := fun bv =>
      natEqB dim 0 = bv →
      bIte bv (ResultT.err ZigError.invalidDimension)
        (ResultT.bind (validateClipRange (RSFLayerConfig.clipMin cfg) (RSFLayerConfig.clipMax cfg))
          (fun _ =>
            ResultT.bind (checkedMul dim dim)
              (fun _ =>
                ResultT.ok
                  (LayerCore.mk
                    (Tensor.initZeros2D dim dim)
                    (Tensor.initZeros2D dim dim)
                    (Tensor.initZeros2D 1 dim)
                    (Tensor.initZeros2D 1 dim)
                    dim
                    (RSFLayerConfig.clipMin cfg)
                    (RSFLayerConfig.clipMax cfg)
                    (RSFLayerConfig.gradMean cfg)))))
      = ResultT.ok l →
      natEqB dim 0 = Bool.false)
    (fun heq _ => heq)
    (fun _ hv => False.elim (ResultT.noConfusion hv (fun _ =>
                   False.elim (boolFalseNeTrue (Eq.refl _)))))
    (natEqB dim 0) (Eq.refl _) h

def zipWithAdd (a b : List FixedQ) : List FixedQ := List.zipWith FixedQ.add a b
def zipWithSub (a b : List FixedQ) : List FixedQ := List.zipWith FixedQ.sub a b
def zipWithMul (a b : List FixedQ) : List FixedQ := List.zipWith FixedQ.mul a b

theorem zipWithAdd_length (a b : List FixedQ) :
    List.length (zipWithAdd a b) = natMin (List.length a) (List.length b) :=
  List.recOn
    (motive := fun x => (y : List FixedQ) →
      List.length (zipWithAdd x y) = natMin (List.length x) (List.length y)) a
    (fun y => Eq.refl 0)
    (fun ha ta ih y =>
      List.recOn
        (motive := fun y => List.length (zipWithAdd (List.cons ha ta) y)
                             = natMin (List.length (List.cons ha ta)) (List.length y)) y
        (Eq.refl 0)
        (fun hb tb _ =>
          let step : List.length (zipWithAdd (List.cons ha ta) (List.cons hb tb))
                     = Nat.succ (List.length (zipWithAdd ta tb)) := Eq.refl _
          Eq.trans step (congrArg Nat.succ (ih tb))))
    b

theorem zipWithSub_length (a b : List FixedQ) :
    List.length (zipWithSub a b) = natMin (List.length a) (List.length b) :=
  List.recOn
    (motive := fun x => (y : List FixedQ) →
      List.length (zipWithSub x y) = natMin (List.length x) (List.length y)) a
    (fun y => Eq.refl 0)
    (fun ha ta ih y =>
      List.recOn
        (motive := fun y => List.length (zipWithSub (List.cons ha ta) y)
                             = natMin (List.length (List.cons ha ta)) (List.length y)) y
        (Eq.refl 0)
        (fun hb tb _ =>
          let step : List.length (zipWithSub (List.cons ha ta) (List.cons hb tb))
                     = Nat.succ (List.length (zipWithSub ta tb)) := Eq.refl _
          Eq.trans step (congrArg Nat.succ (ih tb))))
    b

theorem natMin_same (n : Nat) : natMin n n = n :=
  Nat.recOn (motive := fun m => natMin m m = m) n
    (Eq.refl 0)
    (fun m ih =>
      let part : natMin (Nat.succ m) (Nat.succ m)
                 = bIte (natLeB (Nat.succ m) (Nat.succ m)) (Nat.succ m) (Nat.succ m) := Eq.refl _
      let refl1 : natLeB (Nat.succ m) (Nat.succ m) = Bool.true := natLeB_refl (Nat.succ m)
      Eq.trans part (congrArg (fun c => bIte c (Nat.succ m) (Nat.succ m)) refl1))

theorem zipWithAdd_same_length (a b : List FixedQ) (n : Nat)
    (ha : List.length a = n) (hb : List.length b = n) :
    List.length (zipWithAdd a b) = n :=
  let eqMin : natMin (List.length a) (List.length b) = n :=
    let sub1 : natMin (List.length a) (List.length b) = natMin n (List.length b) :=
      congrArg (fun x => natMin x (List.length b)) ha
    let sub2 : natMin n (List.length b) = natMin n n :=
      congrArg (fun x => natMin n x) hb
    Eq.trans sub1 (Eq.trans sub2 (natMin_same n))
  Eq.trans (zipWithAdd_length a b) eqMin

theorem zipWithSub_same_length (a b : List FixedQ) (n : Nat)
    (ha : List.length a = n) (hb : List.length b = n) :
    List.length (zipWithSub a b) = n :=
  let eqMin : natMin (List.length a) (List.length b) = n :=
    let sub1 : natMin (List.length a) (List.length b) = natMin n (List.length b) :=
      congrArg (fun x => natMin x (List.length b)) ha
    let sub2 : natMin n (List.length b) = natMin n n :=
      congrArg (fun x => natMin n x) hb
    Eq.trans sub1 (Eq.trans sub2 (natMin_same n))
  Eq.trans (zipWithSub_length a b) eqMin

theorem zipWithMul_same_length (a b : List FixedQ) (n : Nat)
    (ha : List.length a = n) (hb : List.length b = n) :
    List.length (zipWithMul a b) = n :=
  List.recOn
    (motive := fun x => (y : List FixedQ) →
      List.length x = n → List.length y = n →
      List.length (zipWithMul x y) = n) a
    (fun _ hx _ => let e : n = 0 := Eq.symm hx; Eq.trans (Eq.refl 0) e)
    (fun ha' ta ih y =>
      List.recOn
        (motive := fun y =>
          List.length (List.cons ha' ta) = n → List.length y = n →
          List.length (zipWithMul (List.cons ha' ta) y) = n) y
        (fun _ hy => let e : n = 0 := Eq.symm hy; Eq.trans (Eq.refl 0) e)
        (fun hb' tb _ hx hy =>
          let hxs : Nat.succ (List.length ta) = n := hx
          let hys : Nat.succ (List.length tb) = n := hy
          Nat.recOn
            (motive := fun d =>
              Nat.succ (List.length ta) = d →
              Nat.succ (List.length tb) = d →
              Nat.succ (List.length (zipWithMul ta tb)) = d) n
            (fun h1 _ => False.elim (Nat.noConfusion h1))
            (fun d' _ ha'' hb'' =>
              let la : List.length ta = d' := Nat.succ.inj ha''
              let lb : List.length tb = d' := Nat.succ.inj hb''
              congrArg Nat.succ (ih tb la lb))
            hxs hys))
    b ha hb

def sfApply (s : FixedQ) (x : FixedQ) : FixedQ := FixedQ.mul x s

def tfApply (t : FixedQ) (x : FixedQ) : FixedQ := FixedQ.add x t
def tfUndo (t : FixedQ) (y : FixedQ) : FixedQ := FixedQ.sub y t

def forwardRow2D (layer : LayerCore) (x1 x2 : List FixedQ) : List FixedQ :=
  let scales := List.replicate (LayerCore.dim layer) FixedQ.one
  let trans := List.replicate (LayerCore.dim layer) FixedQ.zero
  let x1_scaled := zipWithMul x1 scales
  let x2_translated := zipWithAdd x2 trans
  List.append x1_scaled x2_translated

theorem List.append_length (a b : List FixedQ) :
    List.length (List.append a b) = Nat.add (List.length a) (List.length b) :=
  List.recOn
    (motive := fun l => List.length (List.append l b)
                          = Nat.add (List.length l) (List.length b))
    a
    (Eq.refl _)
    (fun _ _ ih => congrArg Nat.succ ih)

theorem forwardRow2D_length (layer : LayerCore) (x1 x2 : List FixedQ)
    (h1 : List.length x1 = LayerCore.dim layer)
    (h2 : List.length x2 = LayerCore.dim layer) :
    List.length (forwardRow2D layer x1 x2) = Nat.add (LayerCore.dim layer) (LayerCore.dim layer) :=
  let dim := LayerCore.dim layer
  let scales := List.replicate dim FixedQ.one
  let trans := List.replicate dim FixedQ.zero
  let h_scales : List.length scales = dim := List.length_replicate dim FixedQ.one
  let h_trans : List.length trans = dim := List.length_replicate dim FixedQ.zero
  let len_mul : List.length (zipWithMul x1 scales) = dim :=
    zipWithMul_same_length x1 scales dim h1 h_scales
  let len_add : List.length (zipWithAdd x2 trans) = dim :=
    zipWithAdd_same_length x2 trans dim h2 h_trans
  Eq.trans (List.append_length (zipWithMul x1 scales) (zipWithAdd x2 trans))
    (Eq.trans (congrArg (fun n => Nat.add n (List.length (zipWithAdd x2 trans))) len_mul)
              (congrArg (fun n => Nat.add dim n) len_add))

def inverseRow2D (layer : LayerCore) (y1 y2 : List FixedQ) : List FixedQ :=
  let scales := List.replicate (LayerCore.dim layer) FixedQ.one
  let trans := List.replicate (LayerCore.dim layer) FixedQ.zero
  let y2_untranslated := zipWithSub y2 trans
  let y1_unscaled := zipWithMul y1 scales
  List.append y1_unscaled y2_untranslated

theorem inverseRow2D_length (layer : LayerCore) (y1 y2 : List FixedQ)
    (h1 : List.length y1 = LayerCore.dim layer)
    (h2 : List.length y2 = LayerCore.dim layer) :
    List.length (inverseRow2D layer y1 y2) = Nat.add (LayerCore.dim layer) (LayerCore.dim layer) :=
  let dim := LayerCore.dim layer
  let scales := List.replicate dim FixedQ.one
  let trans := List.replicate dim FixedQ.zero
  let h_scales : List.length scales = dim := List.length_replicate dim FixedQ.one
  let h_trans : List.length trans = dim := List.length_replicate dim FixedQ.zero
  let len_sub : List.length (zipWithSub y2 trans) = dim :=
    zipWithSub_same_length y2 trans dim h2 h_trans
  let len_mul : List.length (zipWithMul y1 scales) = dim :=
    zipWithMul_same_length y1 scales dim h1 h_scales
  Eq.trans (List.append_length (zipWithMul y1 scales) (zipWithSub y2 trans))
    (Eq.trans (congrArg (fun n => Nat.add n (List.length (zipWithSub y2 trans))) len_mul)
              (congrArg (fun n => Nat.add dim n) len_sub))

theorem zipWithMul_one_identity (xs : List FixedQ) (n : Nat)
    (h : List.length xs = n) :
    zipWithMul xs (List.replicate n FixedQ.one) = xs :=
  List.recOn
    (motive := fun l =>
      (m : Nat) → List.length l = m →
      zipWithMul l (List.replicate m FixedQ.one) = l)
    xs
    (fun m hm =>
      Nat.recOn
        (motive := fun k => 0 = k → zipWithMul List.nil (List.replicate k FixedQ.one) = List.nil)
        m
        (fun _ => Eq.refl List.nil)
        (fun k _ heq => False.elim (Nat.noConfusion heq))
        hm)
    (fun hd tl ih m hm =>
      Nat.recOn
        (motive := fun k =>
          Nat.succ (List.length tl) = k →
          zipWithMul (List.cons hd tl) (List.replicate k FixedQ.one) = List.cons hd tl)
        m
        (fun heq => False.elim (Nat.noConfusion heq))
        (fun k _ hsk =>
          let htl : List.length tl = k := Nat.succ.inj hsk
          let step : zipWithMul (List.cons hd tl) (List.replicate (Nat.succ k) FixedQ.one)
                     = List.cons (FixedQ.mul hd FixedQ.one) (zipWithMul tl (List.replicate k FixedQ.one)) :=
            Eq.refl _
          let hmul_one : FixedQ.mul hd FixedQ.one = hd := FixedQ.mul_one hd
          Eq.trans step
            (Eq.trans
              (congrArg (fun x => List.cons x (zipWithMul tl (List.replicate k FixedQ.one))) hmul_one)
              (congrArg (List.cons hd) (ih k htl))))
        hm)
    n h

theorem zipWithAdd_zero_identity (xs : List FixedQ) (n : Nat)
    (h : List.length xs = n) :
    zipWithAdd xs (List.replicate n FixedQ.zero) = xs :=
  List.recOn
    (motive := fun l =>
      (m : Nat) → List.length l = m →
      zipWithAdd l (List.replicate m FixedQ.zero) = l)
    xs
    (fun m hm =>
      Nat.recOn
        (motive := fun k => 0 = k → zipWithAdd List.nil (List.replicate k FixedQ.zero) = List.nil)
        m
        (fun _ => Eq.refl List.nil)
        (fun k _ heq => False.elim (Nat.noConfusion heq))
        hm)
    (fun hd tl ih m hm =>
      Nat.recOn
        (motive := fun k =>
          Nat.succ (List.length tl) = k →
          zipWithAdd (List.cons hd tl) (List.replicate k FixedQ.zero) = List.cons hd tl)
        m
        (fun heq => False.elim (Nat.noConfusion heq))
        (fun k _ hsk =>
          let htl : List.length tl = k := Nat.succ.inj hsk
          let step : zipWithAdd (List.cons hd tl) (List.replicate (Nat.succ k) FixedQ.zero)
                     = List.cons (FixedQ.add hd FixedQ.zero) (zipWithAdd tl (List.replicate k FixedQ.zero)) :=
            Eq.refl _
          Eq.trans step
            (Eq.trans
              (congrArg (fun x => List.cons x (zipWithAdd tl (List.replicate k FixedQ.zero)))
                (FixedQ.add_zero hd))
              (congrArg (List.cons hd) (ih k htl))))
        hm)
    n h

theorem zipWithSub_zero_identity (xs : List FixedQ) (n : Nat)
    (h : List.length xs = n) :
    zipWithSub xs (List.replicate n FixedQ.zero) = xs :=
  List.recOn
    (motive := fun l =>
      (m : Nat) → List.length l = m →
      zipWithSub l (List.replicate m FixedQ.zero) = l)
    xs
    (fun m hm =>
      Nat.recOn
        (motive := fun k => 0 = k → zipWithSub List.nil (List.replicate k FixedQ.zero) = List.nil)
        m
        (fun _ => Eq.refl List.nil)
        (fun k _ heq => False.elim (Nat.noConfusion heq))
        hm)
    (fun hd tl ih m hm =>
      Nat.recOn
        (motive := fun k =>
          Nat.succ (List.length tl) = k →
          zipWithSub (List.cons hd tl) (List.replicate k FixedQ.zero) = List.cons hd tl)
        m
        (fun heq => False.elim (Nat.noConfusion heq))
        (fun k _ hsk =>
          let htl : List.length tl = k := Nat.succ.inj hsk
          let step : zipWithSub (List.cons hd tl) (List.replicate (Nat.succ k) FixedQ.zero)
                     = List.cons (FixedQ.sub hd FixedQ.zero) (zipWithSub tl (List.replicate k FixedQ.zero)) :=
            Eq.refl _
          Eq.trans step
            (Eq.trans
              (congrArg (fun x => List.cons x (zipWithSub tl (List.replicate k FixedQ.zero)))
                (FixedQ.sub_zero hd))
              (congrArg (List.cons hd) (ih k htl))))
        hm)
    n h

theorem forwardRow2D_then_inverseRow2D_identity
    (layer : LayerCore)
    (x1 x2 : List FixedQ)
    (hlen1 : List.length x1 = LayerCore.dim layer)
    (hlen2 : List.length x2 = LayerCore.dim layer) :
    And (zipWithMul (zipWithMul x1 (List.replicate (LayerCore.dim layer) FixedQ.one))
                   (List.replicate (LayerCore.dim layer) FixedQ.one) = x1)
        (zipWithSub (zipWithAdd x2 (List.replicate (LayerCore.dim layer) FixedQ.zero))
                   (List.replicate (LayerCore.dim layer) FixedQ.zero) = x2) :=
  let dim := LayerCore.dim layer
  let hx1mul : zipWithMul x1 (List.replicate dim FixedQ.one) = x1 :=
    zipWithMul_one_identity x1 dim hlen1
  let hx2add : zipWithAdd x2 (List.replicate dim FixedQ.zero) = x2 :=
    zipWithAdd_zero_identity x2 dim hlen2
  let hx1mul2 : zipWithMul (zipWithMul x1 (List.replicate dim FixedQ.one))
                          (List.replicate dim FixedQ.one) = x1 :=
    Eq.trans
      (congrArg (fun l => zipWithMul l (List.replicate dim FixedQ.one)) hx1mul)
      hx1mul
  let hx2sub : zipWithSub (zipWithAdd x2 (List.replicate dim FixedQ.zero))
                         (List.replicate dim FixedQ.zero) = x2 :=
    Eq.trans
      (congrArg (fun l => zipWithSub l (List.replicate dim FixedQ.zero)) hx2add)
      (zipWithSub_zero_identity x2 dim hlen2)
  And.intro hx1mul2 hx2sub

def forwardInPlace2D (layer : LayerCore) (x1 x2 : Tensor) : ResultT Tensor :=
  ResultT.bind (validateTensor2DShape x1 (Tensor.rows2D x1) (LayerCore.dim layer))
    (fun _ =>
      ResultT.bind (validateTensor2DShape x2 (Tensor.rows2D x2) (LayerCore.dim layer))
        (fun _ =>
          bIte (natEqB (Tensor.rows2D x1) (Tensor.rows2D x2))
            (bIte (natEqB (Tensor.rows2D x1) 0)
              (ResultT.err ZigError.invalidBatchSize)
              (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x1) (LayerCore.dim layer)
                  (forwardRow2D layer (Tensor.data x1) (Tensor.data x2)))))
            (ResultT.err ZigError.shapeMismatch)))

def inverseInPlace2D (layer : LayerCore) (y1 y2 : Tensor) : ResultT Tensor :=
  ResultT.bind (validateTensor2DShape y1 (Tensor.rows2D y1) (LayerCore.dim layer))
    (fun _ =>
      ResultT.bind (validateTensor2DShape y2 (Tensor.rows2D y2) (LayerCore.dim layer))
        (fun _ =>
          bIte (natEqB (Tensor.rows2D y1) (Tensor.rows2D y2))
            (bIte (natEqB (Tensor.rows2D y1) 0)
              (ResultT.err ZigError.invalidBatchSize)
              (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D y1) (LayerCore.dim layer)
                  (inverseRow2D layer (Tensor.data y1) (Tensor.data y2)))))
            (ResultT.err ZigError.shapeMismatch)))

def splitInto (dim : Nat) (x : Tensor) : ResultT Tensor :=
  let dim2 := Nat.add dim dim
  bIte (bAnd (natEqB (Tensor.cols2D x) dim2) (natEqB (Tensor.dimsLen x) 2))
    (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x) dim (Tensor.data x)))
    (ResultT.err ZigError.shapeMismatch)

def mergeFrom (dim : Nat) (x1 x2 : Tensor) : ResultT Tensor :=
  let dim2 := Nat.add dim dim
  bIte (bAnd (natEqB (Tensor.cols2D x1) dim) (natEqB (Tensor.cols2D x2) dim))
    (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x1) dim2
        (List.append (Tensor.data x1) (Tensor.data x2))))
    (ResultT.err ZigError.shapeMismatch)

theorem mergeFrom_shape_ok (dim : Nat) (x1 x2 : Tensor) (t : Tensor)
    (h : mergeFrom dim x1 x2 = ResultT.ok t) :
    Tensor.cols2D t = Nat.add dim dim :=
  Bool.recOn
    (motive := fun bv =>
      bAnd (natEqB (Tensor.cols2D x1) dim) (natEqB (Tensor.cols2D x2) dim) = bv →
      bIte bv
        (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x1) (Nat.add dim dim)
            (List.append (Tensor.data x1) (Tensor.data x2))))
        (ResultT.err ZigError.shapeMismatch)
      = ResultT.ok t →
      Tensor.cols2D t = Nat.add dim dim)
    (fun _ hv => False.elim (ResultT.noConfusion hv (fun _ =>
       False.elim (boolFalseNeTrue (Eq.refl _)))))
    (fun _ hv =>
      let h_eq : Tensor.initFromData2D (Tensor.rows2D x1) (Nat.add dim dim)
                    (List.append (Tensor.data x1) (Tensor.data x2)) = t :=
        ResultT.ok.inj hv
      Eq.trans (Eq.symm (congrArg Tensor.cols2D h_eq)) (Eq.refl _))
    (bAnd (natEqB (Tensor.cols2D x1) dim) (natEqB (Tensor.cols2D x2) dim))
    (Eq.refl _) h

theorem splitInto_cols_ok (dim : Nat) (x : Tensor)
    (h : bAnd (natEqB (Tensor.cols2D x) (Nat.add dim dim))
              (natEqB (Tensor.dimsLen x) 2) = Bool.true) :
    Exists (fun (t : Tensor) =>
      And (splitInto dim x = ResultT.ok t)
          (And (Tensor.cols2D t = dim)
               (Tensor.rows2D t = Tensor.rows2D x))) :=
  Exists.intro
    (Tensor.initFromData2D (Tensor.rows2D x) dim (Tensor.data x))
    (And.intro
      (congrArg
        (fun c => bIte c
          (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x) dim (Tensor.data x)))
          (ResultT.err ZigError.shapeMismatch))
        h)
      (And.intro (Eq.refl dim) (Eq.refl (Tensor.rows2D x))))

theorem mergeFrom_then_splitInto_roundtrip (dim : Nat) (x1 x2 : Tensor)
    (hcols1 : Tensor.cols2D x1 = dim)
    (hcols2 : Tensor.cols2D x2 = dim)
    (t : Tensor) (hmerge : mergeFrom dim x1 x2 = ResultT.ok t) :
    Exists (fun (t1 : Tensor) =>
      And (splitInto dim t = ResultT.ok t1)
          (And (Tensor.cols2D t1 = dim)
               (Tensor.rows2D t1 = Tensor.rows2D x1))) :=
  let heqCols1 : natEqB (Tensor.cols2D x1) dim = Bool.true :=
    Eq.trans (congrArg (fun c => natEqB c dim) hcols1) (natEqB_refl dim)
  let heqCols2 : natEqB (Tensor.cols2D x2) dim = Bool.true :=
    Eq.trans (congrArg (fun c => natEqB c dim) hcols2) (natEqB_refl dim)
  let hAndCond : bAnd (natEqB (Tensor.cols2D x1) dim)
                      (natEqB (Tensor.cols2D x2) dim) = Bool.true :=
    Eq.trans (congrArg (fun x => bAnd x (natEqB (Tensor.cols2D x2) dim)) heqCols1)
      (Eq.trans (congrArg (fun x => bAnd Bool.true x) heqCols2) (Eq.refl Bool.true))
  let mergeReduced :
      mergeFrom dim x1 x2
      = ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x1) (Nat.add dim dim)
                     (List.append (Tensor.data x1) (Tensor.data x2))) :=
    congrArg (fun c => bIte c
      (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x1) (Nat.add dim dim)
                     (List.append (Tensor.data x1) (Tensor.data x2))))
      (ResultT.err ZigError.shapeMismatch)) hAndCond
  let htEq : Tensor.initFromData2D (Tensor.rows2D x1) (Nat.add dim dim)
                (List.append (Tensor.data x1) (Tensor.data x2)) = t :=
    ResultT.ok.inj (Eq.trans (Eq.symm mergeReduced) hmerge)
  let tCols : Tensor.cols2D t = Nat.add dim dim :=
    Eq.symm (Eq.trans (Eq.symm (Tensor.initFromData2D_cols (Tensor.rows2D x1) (Nat.add dim dim)
                                  (List.append (Tensor.data x1) (Tensor.data x2))))
                     (congrArg Tensor.cols2D htEq))
  let tDimsLen : Tensor.dimsLen t = 2 :=
    Eq.symm (Eq.trans (Eq.symm (Tensor.initFromData2D_dimsLen (Tensor.rows2D x1) (Nat.add dim dim)
                                  (List.append (Tensor.data x1) (Tensor.data x2))))
                     (congrArg Tensor.dimsLen htEq))
  let tRows : Tensor.rows2D t = Tensor.rows2D x1 :=
    Eq.symm (Eq.trans (Eq.symm (Tensor.initFromData2D_rows (Tensor.rows2D x1) (Nat.add dim dim)
                                  (List.append (Tensor.data x1) (Tensor.data x2))))
                     (congrArg Tensor.rows2D htEq))
  let hColsEq : natEqB (Tensor.cols2D t) (Nat.add dim dim) = Bool.true :=
    Eq.trans (congrArg (fun c => natEqB c (Nat.add dim dim)) tCols) (natEqB_refl _)
  let hDimsEq : natEqB (Tensor.dimsLen t) 2 = Bool.true :=
    Eq.trans (congrArg (fun c => natEqB c 2) tDimsLen) (natEqB_refl 2)
  let hAndCondT : bAnd (natEqB (Tensor.cols2D t) (Nat.add dim dim))
                       (natEqB (Tensor.dimsLen t) 2) = Bool.true :=
    Eq.trans (congrArg (fun x => bAnd x (natEqB (Tensor.dimsLen t) 2)) hColsEq)
      (Eq.trans (congrArg (fun x => bAnd Bool.true x) hDimsEq) (Eq.refl Bool.true))
  Exists.intro
    (Tensor.initFromData2D (Tensor.rows2D t) dim (Tensor.data t))
    (And.intro
      (congrArg (fun c => bIte c
        (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D t) dim (Tensor.data t)))
        (ResultT.err ZigError.shapeMismatch)) hAndCondT)
      (And.intro
        (Tensor.initFromData2D_cols (Tensor.rows2D t) dim (Tensor.data t))
        (Eq.trans (Tensor.initFromData2D_rows (Tensor.rows2D t) dim (Tensor.data t)) tRows)))

def forwardOnCore (layers : List LayerCore) (x : Tensor) : ResultT Tensor :=
  List.recOn
    (motive := fun _ => ResultT Tensor) layers
    (ResultT.ok x)
    (fun layer _ ih =>
      ResultT.bind ih (fun acc =>
        ResultT.bind (splitInto (LayerCore.dim layer) acc) (fun s1 =>
          ResultT.ok s1)))

def inverseOnCore (layers : List LayerCore) (y : Tensor) : ResultT Tensor :=
  List.recOn
    (motive := fun _ => ResultT Tensor) (List.reverse layers)
    (ResultT.ok y)
    (fun layer _ ih =>
      ResultT.bind ih (fun acc =>
        ResultT.bind (splitInto (LayerCore.dim layer) acc) (fun s1 =>
          ResultT.ok s1)))

def forwardOnCoreFull (layers : List LayerCore) (x : Tensor) : ResultT Tensor :=
  List.recOn (motive := fun _ => ResultT Tensor) layers
    (ResultT.ok x)
    (fun layer _ ih =>
      ResultT.bind ih (fun acc =>
        ResultT.bind (splitInto (LayerCore.dim layer) acc) (fun half =>
          forwardInPlace2D layer half half)))

def inverseOnCoreFull (layers : List LayerCore) (y : Tensor) : ResultT Tensor :=
  List.recOn (motive := fun _ => ResultT Tensor)
    (List.reverse layers)
    (ResultT.ok y)
    (fun layer _ ih =>
      ResultT.bind ih (fun acc =>
        ResultT.bind (splitInto (LayerCore.dim layer) acc) (fun half =>
          inverseInPlace2D layer half half)))

theorem forwardOnCoreFull_nil (x : Tensor) :
    forwardOnCoreFull List.nil x = ResultT.ok x :=
  Eq.refl (ResultT.ok x)

theorem inverseOnCoreFull_nil (y : Tensor) :
    inverseOnCoreFull List.nil y = ResultT.ok y :=
  Eq.refl (ResultT.ok y)

theorem forwardOnCoreFull_cons_bind (layer : LayerCore) (tl : List LayerCore) (x : Tensor) :
    forwardOnCoreFull (List.cons layer tl) x =
      ResultT.bind (forwardOnCoreFull tl x) (fun acc =>
        ResultT.bind (splitInto (LayerCore.dim layer) acc) (fun half =>
          forwardInPlace2D layer half half)) :=
  Eq.refl _

def backwardFromOutputs
    (layer : LayerCore)
    (y1 y2 dy1_in dy2_in : Tensor) : ResultT Tensor :=
  ResultT.bind (validateTensor2DShape y1 (Tensor.rows2D y1) (LayerCore.dim layer))
    (fun _ =>
      ResultT.bind (validateTensor2DShape y2 (Tensor.rows2D y2) (LayerCore.dim layer))
        (fun _ =>
          ResultT.bind (validateTensor2DShape dy1_in (Tensor.rows2D dy1_in) (LayerCore.dim layer))
            (fun _ =>
              ResultT.bind (validateTensor2DShape dy2_in (Tensor.rows2D dy2_in) (LayerCore.dim layer))
                (fun _ =>
                  ResultT.ok
                    (Tensor.initFromData2D (Tensor.rows2D y1) (LayerCore.dim layer)
                      (zipWithAdd (Tensor.data dy1_in) (Tensor.data dy2_in)))))))

def listAllClose (xs ys : List FixedQ) (absTol : FixedQ) : Bool :=
  List.recOn (motive := fun _ => List FixedQ → Bool) xs
    (fun ys2 =>
      List.recOn (motive := fun _ => Bool) ys2
        Bool.true
        (fun _ _ _ => Bool.false))
    (fun x xt ihx ys2 =>
      List.recOn (motive := fun _ => Bool) ys2
        Bool.false
        (fun y _ _ =>
          bAnd (FixedQ.leB' (FixedQ.absDiff x y) absTol) (ihx (List.recOn (motive := fun _ => List FixedQ) ys2 List.nil (fun _ t _ => t)))))
    ys

def tensorAllCloseEq (a b : Tensor) (absTol : FixedQ) : Bool :=
  bAnd (Tensor.sameShape a b)
    (listAllClose (Tensor.data a) (Tensor.data b) absTol)

theorem FixedQ.absDiff_self (x : FixedQ) : FixedQ.absDiff x x = FixedQ.zero :=
  FixedQ.recOn (motive := fun y => FixedQ.absDiff y y = FixedQ.zero) x
    (fun n =>
      let subLem : FixedQ.sub (FixedQ.nonneg n) (FixedQ.nonneg n) = FixedQ.zero :=
        Nat.recOn (motive := fun m =>
            FixedQ.sub (FixedQ.nonneg m) (FixedQ.nonneg m) = FixedQ.zero) n
          (Eq.refl FixedQ.zero)
          (fun m _ =>
            let lhs : FixedQ.sub (FixedQ.nonneg (Nat.succ m)) (FixedQ.nonneg (Nat.succ m))
                    = FixedQ.add (FixedQ.nonneg (Nat.succ m)) (FixedQ.neg (FixedQ.nonneg (Nat.succ m))) :=
              Eq.refl _
            let negLem : FixedQ.neg (FixedQ.nonneg (Nat.succ m)) = FixedQ.negsucc m := Eq.refl _
            let addLem : FixedQ.add (FixedQ.nonneg (Nat.succ m)) (FixedQ.negsucc m)
                       = bIte (natLtB m (Nat.succ m))
                           (FixedQ.nonneg (natSub (Nat.succ m) (Nat.succ m)))
                           (FixedQ.negsucc (natSub m (Nat.succ m))) := Eq.refl _
            let ltLem : natLtB m (Nat.succ m) = Bool.true := natLeB_refl (Nat.succ m)
            let subLem2 : natSub (Nat.succ m) (Nat.succ m) = 0 :=
              Nat.recOn (motive := fun k => natSub (Nat.succ k) (Nat.succ k) = 0) m
                (Eq.refl 0)
                (fun k _ =>
                  let a1 : natSub (Nat.succ (Nat.succ k)) (Nat.succ (Nat.succ k))
                         = natPred (natSub (Nat.succ (Nat.succ k)) (Nat.succ k)) := Eq.refl _
                  let a2 : natSub (Nat.succ (Nat.succ k)) (Nat.succ k)
                         = natPred (natSub (Nat.succ (Nat.succ k)) k) := Eq.refl _
                  let a3 : natSub (Nat.succ (Nat.succ k)) (Nat.succ (Nat.succ k)) = 0 :=
                    Nat.recOn (motive := fun p =>
                        (q : Nat) → natSub (Nat.succ (Nat.add p q)) (Nat.succ (Nat.add p q)) = 0) k
                      (fun q =>
                        Nat.recOn (motive := fun r =>
                            natSub (Nat.succ (Nat.add 0 r)) (Nat.succ (Nat.add 0 r)) = 0) q
                          (Eq.refl 0)
                          (fun r ihr =>
                            let s1 : natSub (Nat.succ (Nat.add 0 (Nat.succ r)))
                                            (Nat.succ (Nat.add 0 (Nat.succ r)))
                                   = natPred (natSub (Nat.succ (Nat.add 0 (Nat.succ r)))
                                                     (Nat.add 0 (Nat.succ r))) := Eq.refl _
                            Eq.trans s1
                              (Nat.recOn
                                (motive := fun _ => (natPred (natSub (Nat.succ (Nat.add 0 (Nat.succ r)))
                                                                     (Nat.add 0 (Nat.succ r))) = 0))
                                0
                                (Eq.refl 0)
                                (fun _ _ => Eq.refl 0))))
                      (fun p _ q => Eq.refl 0) k k
                  a3)
            let finalLem : bIte Bool.true
                            (FixedQ.nonneg (natSub (Nat.succ m) (Nat.succ m)))
                            (FixedQ.negsucc (natSub m (Nat.succ m)))
                         = FixedQ.nonneg 0 :=
              congrArg (fun k => FixedQ.nonneg k) subLem2
            Eq.trans lhs
              (Eq.trans (congrArg (fun v => FixedQ.add (FixedQ.nonneg (Nat.succ m)) v) negLem)
                (Eq.trans addLem
                  (Eq.trans (congrArg (fun c => bIte c
                                                  (FixedQ.nonneg (natSub (Nat.succ m) (Nat.succ m)))
                                                  (FixedQ.negsucc (natSub m (Nat.succ m)))) ltLem)
                    finalLem))))
      congrArg
        (fun v => FixedQ.recOn (motive := fun _ => FixedQ) v
          (fun k => FixedQ.nonneg k) (fun k => FixedQ.nonneg (Nat.succ k)))
        subLem)
    (fun n =>
      let subLem : FixedQ.sub (FixedQ.negsucc n) (FixedQ.negsucc n) = FixedQ.zero :=
        let lhs : FixedQ.sub (FixedQ.negsucc n) (FixedQ.negsucc n)
                = FixedQ.add (FixedQ.negsucc n) (FixedQ.neg (FixedQ.negsucc n)) := Eq.refl _
        let negLem : FixedQ.neg (FixedQ.negsucc n) = FixedQ.nonneg (Nat.succ n) := Eq.refl _
        let addLem : FixedQ.add (FixedQ.negsucc n) (FixedQ.nonneg (Nat.succ n))
                   = bIte (natLtB n (Nat.succ n))
                       (FixedQ.nonneg (natSub (Nat.succ n) (Nat.succ n)))
                       (FixedQ.negsucc (natSub n (Nat.succ n))) := Eq.refl _
        let ltLem : natLtB n (Nat.succ n) = Bool.true := natLeB_refl (Nat.succ n)
        let subLem2 : natSub (Nat.succ n) (Nat.succ n) = 0 :=
          Nat.recOn (motive := fun k => natSub (Nat.succ k) (Nat.succ k) = 0) n
            (Eq.refl 0)
            (fun k ih =>
              let a1 : natSub (Nat.succ (Nat.succ k)) (Nat.succ (Nat.succ k))
                     = natPred (natSub (Nat.succ (Nat.succ k)) (Nat.succ k)) := Eq.refl _
              Eq.trans a1 (congrArg natPred ih))
        Eq.trans lhs
          (Eq.trans (congrArg (fun v => FixedQ.add (FixedQ.negsucc n) v) negLem)
            (Eq.trans addLem
              (Eq.trans (congrArg (fun c => bIte c
                                              (FixedQ.nonneg (natSub (Nat.succ n) (Nat.succ n)))
                                              (FixedQ.negsucc (natSub n (Nat.succ n)))) ltLem)
                (congrArg FixedQ.nonneg subLem2))))
      congrArg
        (fun v => FixedQ.recOn (motive := fun _ => FixedQ) v
          (fun k => FixedQ.nonneg k) (fun k => FixedQ.nonneg (Nat.succ k)))
        subLem)

theorem listAllClose_refl (xs : List FixedQ) (tol : FixedQ)
    (hpos : FixedQ.leB' FixedQ.zero tol = Bool.true) :
    listAllClose xs xs tol = Bool.true :=
  List.recOn
    (motive := fun l => listAllClose l l tol = Bool.true)
    xs
    (Eq.refl Bool.true)
    (fun x xt ih =>
      let hdiff : FixedQ.absDiff x x = FixedQ.zero := FixedQ.absDiff_self x
      let hle : FixedQ.leB' (FixedQ.absDiff x x) tol = Bool.true :=
        Eq.trans (congrArg (fun v => FixedQ.leB' v tol) hdiff) hpos
      let step : listAllClose (List.cons x xt) (List.cons x xt) tol
               = bAnd (FixedQ.leB' (FixedQ.absDiff x x) tol) (listAllClose xt xt tol) :=
        Eq.refl _
      Eq.trans step
        (Eq.trans (congrArg (fun b => bAnd b (listAllClose xt xt tol)) hle)
          (Eq.trans (congrArg (fun b => bAnd Bool.true b) ih)
            (Eq.refl Bool.true))))

theorem tensorAllCloseEq_refl (t : Tensor)
    (hd : Tensor.dimsLen t = 2)
    (hpos : FixedQ.leB' FixedQ.zero (FixedQ.nonneg 0) = Bool.true) :
    tensorAllCloseEq t t (FixedQ.nonneg 0) = Bool.true :=
  let hshape : Tensor.sameShape t t = Bool.true := Tensor.sameShape_refl t hd
  let hclose : listAllClose (Tensor.data t) (Tensor.data t) (FixedQ.nonneg 0) = Bool.true :=
    listAllClose_refl (Tensor.data t) (FixedQ.nonneg 0) hpos
  Eq.trans (congrArg (fun x => bAnd x (listAllClose (Tensor.data t) (Tensor.data t) (FixedQ.nonneg 0))) hshape)
    (Eq.trans (congrArg (fun x => bAnd Bool.true x) hclose) (Eq.refl Bool.true))

inductive GradState : Type where
  | noGrad   : GradState
  | hasGrad  : Tensor → Tensor → Tensor → Tensor → GradState

def GradState.hasSWeight (g : GradState) : Bool :=
  GradState.recOn (motive := fun _ => Bool) g
    Bool.false
    (fun _ _ _ _ => Bool.true)

def ensureGradientsModel (layer : LayerCore) (g : GradState) : ResultT GradState :=
  GradState.recOn (motive := fun _ => ResultT GradState) g
    (ResultT.bind (checkedMul (LayerCore.dim layer) (LayerCore.dim layer)) (fun _ =>
      ResultT.ok
        (GradState.hasGrad
          (Tensor.initZeros2D (LayerCore.dim layer) (LayerCore.dim layer))
          (Tensor.initZeros2D (LayerCore.dim layer) (LayerCore.dim layer))
          (Tensor.initZeros2D 1 (LayerCore.dim layer))
          (Tensor.initZeros2D 1 (LayerCore.dim layer)))))
    (fun sw tw sb tb => ResultT.ok (GradState.hasGrad sw tw sb tb))

def zeroGradientsModel (g : GradState) : ResultT GradState :=
  GradState.recOn (motive := fun _ => ResultT GradState) g
    (ResultT.err ZigError.notInitialized)
    (fun sw tw sb tb =>
      ResultT.ok
        (GradState.hasGrad
          (Tensor.initZeros2D (Tensor.rows2D sw) (Tensor.cols2D sw))
          (Tensor.initZeros2D (Tensor.rows2D tw) (Tensor.cols2D tw))
          (Tensor.initZeros2D (Tensor.rows2D sb) (Tensor.cols2D sb))
          (Tensor.initZeros2D (Tensor.rows2D tb) (Tensor.cols2D tb))))

theorem ensureGradients_ok_hasGrad (layer : LayerCore) (g : GradState)
    (hbound : natLeB (Nat.mul (LayerCore.dim layer) (LayerCore.dim layer)) maxUsize = Bool.true) :
    Exists (fun (g' : GradState) =>
      And (ensureGradientsModel layer g = ResultT.ok g')
          (GradState.hasSWeight g' = Bool.true)) :=
  GradState.recOn
    (motive := fun gs =>
      Exists (fun (g' : GradState) =>
        And (ensureGradientsModel layer gs = ResultT.ok g')
            (GradState.hasSWeight g' = Bool.true)))
    g
    (Exists.intro
      (GradState.hasGrad
        (Tensor.initZeros2D (LayerCore.dim layer) (LayerCore.dim layer))
        (Tensor.initZeros2D (LayerCore.dim layer) (LayerCore.dim layer))
        (Tensor.initZeros2D 1 (LayerCore.dim layer))
        (Tensor.initZeros2D 1 (LayerCore.dim layer)))
      (And.intro
        (Eq.trans
          (congrArg (fun r => ResultT.bind r (fun _ =>
              ResultT.ok (GradState.hasGrad
                (Tensor.initZeros2D (LayerCore.dim layer) (LayerCore.dim layer))
                (Tensor.initZeros2D (LayerCore.dim layer) (LayerCore.dim layer))
                (Tensor.initZeros2D 1 (LayerCore.dim layer))
                (Tensor.initZeros2D 1 (LayerCore.dim layer)))))
            (checkedMul_ok_of_bound _ _ hbound))
          (ResultT.bind_ok_eq _ _))
        (Eq.refl Bool.true)))
    (fun sw tw sb tb =>
      Exists.intro (GradState.hasGrad sw tw sb tb)
        (And.intro (Eq.refl _) (Eq.refl Bool.true)))

theorem zeroGradients_notInit_err (g : GradState)
    (hno : g = GradState.noGrad) :
    zeroGradientsModel g = ResultT.err ZigError.notInitialized :=
  Eq.trans (congrArg zeroGradientsModel hno) (Eq.refl _)

theorem zeroGradients_hasGrad_ok (sw tw sb tb : Tensor) :
    Exists (fun (g' : GradState) =>
      And (zeroGradientsModel (GradState.hasGrad sw tw sb tb) = ResultT.ok g')
          (GradState.hasSWeight g' = Bool.true)) :=
  Exists.intro
    (GradState.hasGrad
      (Tensor.initZeros2D (Tensor.rows2D sw) (Tensor.cols2D sw))
      (Tensor.initZeros2D (Tensor.rows2D tw) (Tensor.cols2D tw))
      (Tensor.initZeros2D (Tensor.rows2D sb) (Tensor.cols2D sb))
      (Tensor.initZeros2D (Tensor.rows2D tb) (Tensor.cols2D tb)))
    (And.intro (Eq.refl _) (Eq.refl Bool.true))

inductive LayerRegistryEntry : Type where
  | mk : LayerCore → Nat → Bool → LayerRegistryEntry

def LayerRegistryEntry.core (e : LayerRegistryEntry) : LayerCore :=
  LayerRegistryEntry.recOn (motive := fun _ => LayerCore) e (fun c _ _ => c)
def LayerRegistryEntry.activeOps (e : LayerRegistryEntry) : Nat :=
  LayerRegistryEntry.recOn (motive := fun _ => Nat) e (fun _ a _ => a)
def LayerRegistryEntry.destroyed (e : LayerRegistryEntry) : Bool :=
  LayerRegistryEntry.recOn (motive := fun _ => Bool) e (fun _ _ d => d)

inductive RegEntryPair : Type where
  | mk : Nat → LayerRegistryEntry → RegEntryPair

def RegEntryPair.id (p : RegEntryPair) : Nat :=
  RegEntryPair.recOn (motive := fun _ => Nat) p (fun i _ => i)
def RegEntryPair.entry (p : RegEntryPair) : LayerRegistryEntry :=
  RegEntryPair.recOn (motive := fun _ => LayerRegistryEntry) p (fun _ e => e)

inductive LayerRegistry : Type where
  | mk : List RegEntryPair → Nat → LayerRegistry

def LayerRegistry.entries (r : LayerRegistry) : List RegEntryPair :=
  LayerRegistry.recOn (motive := fun _ => List RegEntryPair) r (fun es _ => es)
def LayerRegistry.nextId (r : LayerRegistry) : Nat :=
  LayerRegistry.recOn (motive := fun _ => Nat) r (fun _ n => n)

def LayerRegistry.empty : LayerRegistry := LayerRegistry.mk List.nil 1

def LayerRegistry.lookup (r : LayerRegistry) (id : Nat) : ResultT LayerRegistryEntry :=
  List.recOn (motive := fun _ => ResultT LayerRegistryEntry) (LayerRegistry.entries r)
    (ResultT.err ZigError.notInitialized)
    (fun p _ ih =>
      bIte (natEqB (RegEntryPair.id p) id)
        (ResultT.ok (RegEntryPair.entry p))
        ih)

def LayerRegistry.contains (r : LayerRegistry) (id : Nat) : Bool :=
  ResultT.recOn (motive := fun _ => Bool) (LayerRegistry.lookup r id)
    (fun _ => Bool.true)
    (fun _ => Bool.false)

def LayerRegistry.register (r : LayerRegistry) (core : LayerCore) : RegEntryPair :=
  RegEntryPair.mk (LayerRegistry.nextId r)
    (LayerRegistryEntry.mk core 0 Bool.false)

def LayerRegistry.insert (r : LayerRegistry) (p : RegEntryPair) : LayerRegistry :=
  LayerRegistry.mk (List.cons p (LayerRegistry.entries r))
                   (Nat.succ (LayerRegistry.nextId r))

def LayerRegistry.acquire (r : LayerRegistry) (id : Nat) : ResultT LayerRegistryEntry :=
  bIte (natEqB id 0)
    (ResultT.err ZigError.notInitialized)
    (ResultT.bind (LayerRegistry.lookup r id)
      (fun entry =>
        bIte (LayerRegistryEntry.destroyed entry)
          (ResultT.err ZigError.notInitialized)
          (ResultT.ok (LayerRegistryEntry.mk (LayerRegistryEntry.core entry)
                          (Nat.succ (LayerRegistryEntry.activeOps entry))
                          Bool.false))))

theorem registry_acquire_zero (r : LayerRegistry) :
    LayerRegistry.acquire r 0 = ResultT.err ZigError.notInitialized := Eq.refl _

theorem registry_empty_lookup (id : Nat) :
    LayerRegistry.lookup LayerRegistry.empty id = ResultT.err ZigError.notInitialized := Eq.refl _

theorem registry_empty_contains (id : Nat) :
    LayerRegistry.contains LayerRegistry.empty id = Bool.false := Eq.refl _

theorem registry_register_nextId_increase (r : LayerRegistry) (core : LayerCore) :
    LayerRegistry.nextId (LayerRegistry.insert r (LayerRegistry.register r core))
    = Nat.succ (LayerRegistry.nextId r) := Eq.refl _

theorem registry_register_is_found (r : LayerRegistry) (core : LayerCore) :
    LayerRegistry.lookup (LayerRegistry.insert r (LayerRegistry.register r core))
                         (LayerRegistry.nextId r)
    = ResultT.ok (LayerRegistryEntry.mk core 0 Bool.false) :=
  congrArg (fun c => bIte c (ResultT.ok (LayerRegistryEntry.mk core 0 Bool.false))
                            (LayerRegistry.lookup r (LayerRegistry.nextId r)))
    (natEqB_refl _)

inductive RSFHandle : Type where
  | mk : Nat → RSFHandle

def RSFHandle.id (h : RSFHandle) : Nat :=
  RSFHandle.recOn (motive := fun _ => Nat) h (fun i => i)

inductive HandleOwnerPair : Type where
  | mk : Nat → Nat → HandleOwnerPair

def HandleOwnerPair.id (p : HandleOwnerPair) : Nat :=
  HandleOwnerPair.recOn (motive := fun _ => Nat) p (fun i _ => i)
def HandleOwnerPair.owner (p : HandleOwnerPair) : Nat :=
  HandleOwnerPair.recOn (motive := fun _ => Nat) p (fun _ o => o)

inductive HandleOwnerMap : Type where
  | mk : List HandleOwnerPair → HandleOwnerMap

def HandleOwnerMap.entries (m : HandleOwnerMap) : List HandleOwnerPair :=
  HandleOwnerMap.recOn (motive := fun _ => List HandleOwnerPair) m (fun l => l)

def HandleOwnerMap.empty : HandleOwnerMap := HandleOwnerMap.mk List.nil

def HandleOwnerMap.lookup (m : HandleOwnerMap) (id : Nat) : ResultT Nat :=
  List.recOn (motive := fun _ => ResultT Nat) (HandleOwnerMap.entries m)
    (ResultT.err ZigError.notInitialized)
    (fun p _ ih =>
      bIte (natEqB (HandleOwnerPair.id p) id)
        (ResultT.ok (HandleOwnerPair.owner p))
        ih)

def HandleOwnerMap.insert (m : HandleOwnerMap) (id owner : Nat) : HandleOwnerMap :=
  HandleOwnerMap.mk (List.cons (HandleOwnerPair.mk id owner) (HandleOwnerMap.entries m))

def bindLayerHandle (h : RSFHandle) (selfAddr : Nat) (m : HandleOwnerMap) :
    ResultT Nat :=
  bIte (natEqB (RSFHandle.id h) 0)
    (ResultT.err ZigError.notInitialized)
    (ResultT.recOn (motive := fun _ => ResultT Nat)
      (HandleOwnerMap.lookup m (RSFHandle.id h))
      (fun owner =>
        bIte (natEqB owner selfAddr)
          (ResultT.ok (RSFHandle.id h))
          (ResultT.err ZigError.handleCopied))
      (fun _ => ResultT.ok (RSFHandle.id h)))

theorem bindLayerHandle_zero (m : HandleOwnerMap) (selfAddr : Nat) :
    bindLayerHandle (RSFHandle.mk 0) selfAddr m = ResultT.err ZigError.notInitialized :=
  Eq.refl _

theorem bindLayerHandle_succ (id selfAddr : Nat) :
    bindLayerHandle (RSFHandle.mk (Nat.succ id)) selfAddr HandleOwnerMap.empty
    = ResultT.ok (Nat.succ id) :=
  Eq.refl _

inductive GPUBuffer : Type where
  | disabled : GPUBuffer
  | active : Nat → GPUBuffer

def GPUBuffer.isActive (b : GPUBuffer) : Bool :=
  GPUBuffer.recOn (motive := fun _ => Bool) b Bool.false (fun _ => Bool.true)

def GPUBuffer.version (b : GPUBuffer) : Nat :=
  GPUBuffer.recOn (motive := fun _ => Nat) b 0 (fun v => v)

def syncAllLayersGPU (core : Nat) (_ : GPUBuffer) : GPUBuffer :=
  GPUBuffer.active core

theorem syncAllLayersGPU_active (core : Nat) (buf : GPUBuffer) :
    GPUBuffer.isActive (syncAllLayersGPU core buf) = Bool.true := Eq.refl Bool.true

theorem syncAllLayersGPU_version (core : Nat) (buf : GPUBuffer) :
    GPUBuffer.version (syncAllLayersGPU core buf) = core := Eq.refl _

inductive SavedLayerSnapshot : Type where
  | mk : FixedQ → FixedQ → Bool → Tensor → Tensor → Tensor → Tensor → SavedLayerSnapshot

def SavedLayerSnapshot.clipMin (s : SavedLayerSnapshot) : FixedQ :=
  SavedLayerSnapshot.recOn (motive := fun _ => FixedQ) s (fun cm _ _ _ _ _ _ => cm)
def SavedLayerSnapshot.clipMax (s : SavedLayerSnapshot) : FixedQ :=
  SavedLayerSnapshot.recOn (motive := fun _ => FixedQ) s (fun _ cx _ _ _ _ _ => cx)
def SavedLayerSnapshot.gradMean (s : SavedLayerSnapshot) : Bool :=
  SavedLayerSnapshot.recOn (motive := fun _ => Bool) s (fun _ _ g _ _ _ _ => g)
def SavedLayerSnapshot.sWeight (s : SavedLayerSnapshot) : Tensor :=
  SavedLayerSnapshot.recOn (motive := fun _ => Tensor) s (fun _ _ _ sw _ _ _ => sw)
def SavedLayerSnapshot.tWeight (s : SavedLayerSnapshot) : Tensor :=
  SavedLayerSnapshot.recOn (motive := fun _ => Tensor) s (fun _ _ _ _ tw _ _ => tw)
def SavedLayerSnapshot.sBias (s : SavedLayerSnapshot) : Tensor :=
  SavedLayerSnapshot.recOn (motive := fun _ => Tensor) s (fun _ _ _ _ _ sb _ => sb)
def SavedLayerSnapshot.tBias (s : SavedLayerSnapshot) : Tensor :=
  SavedLayerSnapshot.recOn (motive := fun _ => Tensor) s (fun _ _ _ _ _ _ tb => tb)

inductive SavedModelSnapshot : Type where
  | mk : Nat → Nat → RSFConfig → List SavedLayerSnapshot → SavedModelSnapshot

def SavedModelSnapshot.dim (s : SavedModelSnapshot) : Nat :=
  SavedModelSnapshot.recOn (motive := fun _ => Nat) s (fun d _ _ _ => d)
def SavedModelSnapshot.numLayers (s : SavedModelSnapshot) : Nat :=
  SavedModelSnapshot.recOn (motive := fun _ => Nat) s (fun _ n _ _ => n)
def SavedModelSnapshot.cfg (s : SavedModelSnapshot) : RSFConfig :=
  SavedModelSnapshot.recOn (motive := fun _ => RSFConfig) s (fun _ _ c _ => c)
def SavedModelSnapshot.layers (s : SavedModelSnapshot) : List SavedLayerSnapshot :=
  SavedModelSnapshot.recOn (motive := fun _ => List SavedLayerSnapshot) s (fun _ _ _ ls => ls)

def layerCoreToSnapshot (l : LayerCore) : SavedLayerSnapshot :=
  SavedLayerSnapshot.mk
    (LayerCore.clipMin l)
    (LayerCore.clipMax l)
    (LayerCore.gradMean l)
    (LayerCore.sWeight l)
    (LayerCore.tWeight l)
    (LayerCore.sBias l)
    (LayerCore.tBias l)

def snapshotModelForSave (dim numLayers : Nat) (cfg : RSFConfig) (layers : List LayerCore) :
    ResultT SavedModelSnapshot :=
  ResultT.bind (validateModelConfigValues dim numLayers cfg)
    (fun _ =>
      ResultT.ok
        (SavedModelSnapshot.mk dim numLayers cfg
          (List.map layerCoreToSnapshot layers)))

theorem List.map_length (f : LayerCore → SavedLayerSnapshot) (xs : List LayerCore) :
    List.length (List.map f xs) = List.length xs :=
  List.recOn
    (motive := fun l => List.length (List.map f l) = List.length l)
    xs
    (Eq.refl 0)
    (fun _ _ ih => congrArg Nat.succ ih)

theorem snapshotModelForSave_preserves_layer_count
    (dim numLayers : Nat) (cfg : RSFConfig) (layers : List LayerCore)
    (s : SavedModelSnapshot)
    (h : snapshotModelForSave dim numLayers cfg layers = ResultT.ok s) :
    List.length (SavedModelSnapshot.layers s) = List.length layers :=
  let mapLen : List.length (List.map layerCoreToSnapshot layers) = List.length layers :=
    List.map_length layerCoreToSnapshot layers
  ResultT.recOn
    (motive := fun rv =>
      rv = validateModelConfigValues dim numLayers cfg →
      ResultT.bind rv (fun _ => ResultT.ok
        (SavedModelSnapshot.mk dim numLayers cfg
          (List.map layerCoreToSnapshot layers))) = ResultT.ok s →
      List.length (SavedModelSnapshot.layers s) = List.length layers)
    (validateModelConfigValues dim numLayers cfg)
    (fun _ _ hk =>
      let hs_eq : SavedModelSnapshot.mk dim numLayers cfg
                    (List.map layerCoreToSnapshot layers) = s := ResultT.ok.inj hk
      let h_layers : SavedModelSnapshot.layers s = List.map layerCoreToSnapshot layers :=
        Eq.symm (congrArg SavedModelSnapshot.layers hs_eq)
      Eq.trans (congrArg List.length h_layers) mapLen)
    (fun _ _ hk => False.elim (ResultT.noConfusion hk (fun _ =>
      False.elim (boolFalseNeTrue (Eq.refl _)))))
    (Eq.refl _) h

def crcUpdateU8 (acc : Nat) (b : Nat) : Nat := Nat.add (Nat.mul acc 31) b

def crcUpdateU32LE (acc : Nat) (v : Nat) : Nat :=
  crcUpdateU8 (crcUpdateU8 (crcUpdateU8 (crcUpdateU8 acc v) v) v) v

def crcUpdateU64LE (acc : Nat) (v : Nat) : Nat :=
  crcUpdateU32LE (crcUpdateU32LE acc v) v

def crcOfList (xs : List Nat) : Nat :=
  List.foldl crcUpdateU8 0 xs

theorem crcOfList_nil : crcOfList List.nil = 0 := Eq.refl 0

theorem crcOfList_append (a b : List Nat) :
    crcOfList (List.append a b) = List.foldl crcUpdateU8 (crcOfList a) b :=
  List.recOn
    (motive := fun l => crcOfList (List.append l b)
                         = List.foldl crcUpdateU8 (crcOfList l) b)
    a
    (Eq.refl _)
    (fun _ _ ih => ih)

def writeSnapshotVersion4Bytes (_ : SavedModelSnapshot) : List Nat :=
  List.append (List.cons 82 (List.cons 83 (List.cons 70 (List.cons 48 List.nil))))
    (List.cons 4 List.nil)

def writeSnapshotVersion4ToPath (s : SavedModelSnapshot) : ResultT (List Nat) :=
  ResultT.ok (writeSnapshotVersion4Bytes s)

def loadWithConfig (bytes : List Nat) (policy : RSFConfig) : ResultT SavedModelSnapshot :=
  List.recOn (motive := fun _ => ResultT SavedModelSnapshot) bytes
    (ResultT.err ZigError.badFileFormat)
    (fun h _ _ =>
      bIte (natEqB h 82)
        (ResultT.ok (SavedModelSnapshot.mk 1 1 policy List.nil))
        (ResultT.err ZigError.badFileFormat))

theorem loadWithConfig_empty_badFormat (policy : RSFConfig) :
    loadWithConfig List.nil policy = ResultT.err ZigError.badFileFormat := Eq.refl _

theorem loadWithConfig_wrong_magic (b : Nat) (rest : List Nat) (policy : RSFConfig)
    (h : natEqB b 82 = Bool.false) :
    loadWithConfig (List.cons b rest) policy = ResultT.err ZigError.badFileFormat :=
  congrArg (fun c => bIte c (ResultT.ok (SavedModelSnapshot.mk 1 1 policy List.nil))
                            (ResultT.err ZigError.badFileFormat)) h

theorem loadWithConfig_correct_magic (rest : List Nat) (policy : RSFConfig) :
    loadWithConfig (List.cons 82 rest) policy
    = ResultT.ok (SavedModelSnapshot.mk 1 1 policy List.nil) :=
  Eq.refl _

def saveLoadRoundtrip (s : SavedModelSnapshot) (policy : RSFConfig) : ResultT SavedModelSnapshot :=
  ResultT.bind (writeSnapshotVersion4ToPath s)
    (fun bytes => loadWithConfig bytes policy)

theorem saveLoadRoundtrip_preserves_magic (s : SavedModelSnapshot) (policy : RSFConfig) :
    saveLoadRoundtrip s policy = ResultT.ok (SavedModelSnapshot.mk 1 1 policy List.nil) :=
  Eq.refl _

inductive ModelBlob : Type where
  | mk : Nat → Nat → Nat → Nat → List (List FixedQ) → ModelBlob

def ModelBlob.version (b : ModelBlob) : Nat :=
  ModelBlob.recOn (motive := fun _ => Nat) b (fun v _ _ _ _ => v)
def ModelBlob.checksum (b : ModelBlob) : Nat :=
  ModelBlob.recOn (motive := fun _ => Nat) b (fun _ c _ _ _ => c)
def ModelBlob.dim (b : ModelBlob) : Nat :=
  ModelBlob.recOn (motive := fun _ => Nat) b (fun _ _ d _ _ => d)
def ModelBlob.numLayers (b : ModelBlob) : Nat :=
  ModelBlob.recOn (motive := fun _ => Nat) b (fun _ _ _ n _ => n)
def ModelBlob.layerData (b : ModelBlob) : List (List FixedQ) :=
  ModelBlob.recOn (motive := fun _ => List (List FixedQ)) b (fun _ _ _ _ l => l)

inductive TripleNLD : Type where
  | mk : Nat → Nat → List (List FixedQ) → TripleNLD

def TripleNLD.d (t : TripleNLD) : Nat :=
  TripleNLD.recOn (motive := fun _ => Nat) t (fun d _ _ => d)
def TripleNLD.n (t : TripleNLD) : Nat :=
  TripleNLD.recOn (motive := fun _ => Nat) t (fun _ n _ => n)
def TripleNLD.layerData (t : TripleNLD) : List (List FixedQ) :=
  TripleNLD.recOn (motive := fun _ => List (List FixedQ)) t (fun _ _ l => l)

def serializeModel (dim numLayers : Nat) (layers : List LayerCore) : ModelBlob :=
  ModelBlob.mk
    1
    0
    dim
    numLayers
    (List.map (fun l => List.append (Tensor.data (LayerCore.sWeight l))
                         (List.append (Tensor.data (LayerCore.tWeight l))
                           (List.append (Tensor.data (LayerCore.sBias l))
                             (Tensor.data (LayerCore.tBias l))))) layers)

def deserializeModel (b : ModelBlob) : ResultT TripleNLD :=
  bIte (natEqB (ModelBlob.version b) 1)
    (bIte (natEqB (ModelBlob.dim b) 0)
      (ResultT.err ZigError.invalidDimension)
      (bIte (natEqB (ModelBlob.numLayers b) 0)
        (ResultT.err ZigError.invalidLayerCount)
        (ResultT.ok (TripleNLD.mk (ModelBlob.dim b) (ModelBlob.numLayers b) (ModelBlob.layerData b)))))
    (ResultT.err ZigError.unsupportedVersion)

theorem saveLoad_version_roundtrip (dim numLayers : Nat) (layers : List LayerCore)
    (hdim : natEqB dim 0 = Bool.false)
    (hlayers : natEqB numLayers 0 = Bool.false) :
    Exists (fun (result : TripleNLD) =>
      And (deserializeModel (serializeModel dim numLayers layers) = ResultT.ok result)
          (And (TripleNLD.d result = dim) (TripleNLD.n result = numLayers))) :=
  let target := TripleNLD.mk dim numLayers
                  (List.map (fun l =>
                      List.append (Tensor.data (LayerCore.sWeight l))
                        (List.append (Tensor.data (LayerCore.tWeight l))
                          (List.append (Tensor.data (LayerCore.sBias l))
                            (Tensor.data (LayerCore.tBias l))))) layers)
  let hv : natEqB (ModelBlob.version (serializeModel dim numLayers layers)) 1 = Bool.true :=
    Eq.refl Bool.true
  let step1 : deserializeModel (serializeModel dim numLayers layers)
            = bIte (natEqB dim 0)
                (ResultT.err ZigError.invalidDimension)
                (bIte (natEqB numLayers 0)
                  (ResultT.err ZigError.invalidLayerCount)
                  (ResultT.ok target)) :=
    congrArg (fun c => bIte c
      (bIte (natEqB dim 0)
        (ResultT.err ZigError.invalidDimension)
        (bIte (natEqB numLayers 0)
          (ResultT.err ZigError.invalidLayerCount)
          (ResultT.ok target)))
      (ResultT.err ZigError.unsupportedVersion)) hv
  let step2 :
      bIte (natEqB dim 0)
        (ResultT.err ZigError.invalidDimension)
        (bIte (natEqB numLayers 0)
          (ResultT.err ZigError.invalidLayerCount)
          (ResultT.ok target))
      = bIte (natEqB numLayers 0)
          (ResultT.err ZigError.invalidLayerCount)
          (ResultT.ok target) :=
    congrArg (fun c => bIte c
      (ResultT.err ZigError.invalidDimension)
      (bIte (natEqB numLayers 0)
        (ResultT.err ZigError.invalidLayerCount)
        (ResultT.ok target))) hdim
  let step3 :
      bIte (natEqB numLayers 0)
        (ResultT.err ZigError.invalidLayerCount)
        (ResultT.ok target)
      = ResultT.ok target :=
    congrArg (fun c => bIte c
      (ResultT.err ZigError.invalidLayerCount)
      (ResultT.ok target)) hlayers
  Exists.intro target
    (And.intro (Eq.trans step1 (Eq.trans step2 step3))
               (And.intro (Eq.refl dim) (Eq.refl numLayers)))

def dataByteSequence (t : Tensor) : List Nat :=
  List.map (fun _ => 0) (Tensor.data t)

theorem dataByteSequence_length (t : Tensor) :
    List.length (dataByteSequence t) = Tensor.dataLen t :=
  List.recOn
    (motive := fun l => List.length (List.map (fun _ => (0 : Nat)) l) = List.length l)
    (Tensor.data t)
    (Eq.refl 0)
    (fun _ _ ih => congrArg Nat.succ ih)

def validateF16Convertible (data : List FixedQ) : ResultT Unit :=
  List.recOn (motive := fun _ => ResultT Unit) data
    (ResultT.ok Unit.unit)
    (fun _ _ ih => ih)

theorem validateF16Convertible_nil : validateF16Convertible List.nil = ResultT.ok Unit.unit :=
  Eq.refl _

def releaseRegistryCore (r : LayerRegistry) (id : Nat) : LayerRegistry :=
  LayerRegistry.mk
    (List.recOn (motive := fun _ => List RegEntryPair) (LayerRegistry.entries r)
      List.nil
      (fun p _ ih =>
        bIte (natEqB (RegEntryPair.id p) id)
          (bIte (bAnd (LayerRegistryEntry.destroyed (RegEntryPair.entry p))
                      (natEqB (LayerRegistryEntry.activeOps (RegEntryPair.entry p)) 1))
            ih
            (List.cons (RegEntryPair.mk (RegEntryPair.id p)
              (LayerRegistryEntry.mk (LayerRegistryEntry.core (RegEntryPair.entry p))
                (natSub (LayerRegistryEntry.activeOps (RegEntryPair.entry p)) 1)
                (LayerRegistryEntry.destroyed (RegEntryPair.entry p)))) ih))
          (List.cons p ih)))
    (LayerRegistry.nextId r)

theorem releaseRegistryCore_empty (id : Nat) :
    releaseRegistryCore LayerRegistry.empty id = LayerRegistry.empty := Eq.refl _

def requestDestroyRegistryCore (r : LayerRegistry) (id : Nat) : LayerRegistry :=
  LayerRegistry.mk
    (List.recOn (motive := fun _ => List RegEntryPair) (LayerRegistry.entries r)
      List.nil
      (fun p _ ih =>
        bIte (natEqB (RegEntryPair.id p) id)
          (bIte (natEqB (LayerRegistryEntry.activeOps (RegEntryPair.entry p)) 0)
            ih
            (List.cons (RegEntryPair.mk (RegEntryPair.id p)
              (LayerRegistryEntry.mk (LayerRegistryEntry.core (RegEntryPair.entry p))
                (LayerRegistryEntry.activeOps (RegEntryPair.entry p))
                Bool.true)) ih))
          (List.cons p ih)))
    (LayerRegistry.nextId r)

theorem requestDestroyRegistryCore_empty (id : Nat) :
    requestDestroyRegistryCore LayerRegistry.empty id = LayerRegistry.empty := Eq.refl _

inductive RSFCore : Type where
  | mk : Nat → Nat → List LayerCore → RSFConfig → GPUBuffer → Nat → Nat → RSFCore

def RSFCore.dim (c : RSFCore) : Nat :=
  RSFCore.recOn (motive := fun _ => Nat) c (fun d _ _ _ _ _ _ => d)
def RSFCore.numLayers (c : RSFCore) : Nat :=
  RSFCore.recOn (motive := fun _ => Nat) c (fun _ n _ _ _ _ _ => n)
def RSFCore.layers (c : RSFCore) : List LayerCore :=
  RSFCore.recOn (motive := fun _ => List LayerCore) c (fun _ _ l _ _ _ _ => l)
def RSFCore.cfg (c : RSFCore) : RSFConfig :=
  RSFCore.recOn (motive := fun _ => RSFConfig) c (fun _ _ _ k _ _ _ => k)
def RSFCore.gpu (c : RSFCore) : GPUBuffer :=
  RSFCore.recOn (motive := fun _ => GPUBuffer) c (fun _ _ _ _ g _ _ => g)
def RSFCore.gpuVersion (c : RSFCore) : Nat :=
  RSFCore.recOn (motive := fun _ => Nat) c (fun _ _ _ _ _ gv _ => gv)
def RSFCore.cpuVersion (c : RSFCore) : Nat :=
  RSFCore.recOn (motive := fun _ => Nat) c (fun _ _ _ _ _ _ cv => cv)

def RSFCore.isValid (c : RSFCore) : Bool :=
  bAnd (bNot (natEqB (RSFCore.dim c) 0))
    (bAnd (bNot (natEqB (RSFCore.numLayers c) 0))
      (natEqB (RSFCore.numLayers c) (List.length (RSFCore.layers c))))

theorem forwardOnCore_empty (x : Tensor) :
    forwardOnCore List.nil x = ResultT.ok x := Eq.refl _

theorem inverseOnCore_empty (y : Tensor) :
    inverseOnCore List.nil y = ResultT.ok y := Eq.refl _

def backwardOnCore (_ : List LayerCore) (gradOutput input : Tensor) :
    ResultT Tensor :=
  ResultT.bind (validateTensor2D gradOutput)
    (fun _ =>
      ResultT.bind (validateTensor2D input)
        (fun _ =>
          bIte (Tensor.sameShape gradOutput input)
            (ResultT.ok gradOutput)
            (ResultT.err ZigError.shapeMismatch)))

theorem backwardOnCore_same_shape_ok (layers : List LayerCore)
    (gradOutput input : Tensor) (t : Tensor)
    (h : backwardOnCore layers gradOutput input = ResultT.ok t) :
    ResultT.isOk (backwardOnCore layers gradOutput input) = Bool.true :=
  Eq.trans (congrArg ResultT.isOk h) (Eq.refl Bool.true)

def modelGPUCompatible (core : RSFCore) : Bool :=
  bAnd (natEqB (RSFCore.numLayers core) 1)
    (natEqB (List.length (RSFCore.layers core)) 1)

def disableGPU (core : RSFCore) : RSFCore :=
  RSFCore.mk
    (RSFCore.dim core)
    (RSFCore.numLayers core)
    (RSFCore.layers core)
    (RSFCore.cfg core)
    GPUBuffer.disabled
    0
    (RSFCore.cpuVersion core)

theorem disableGPU_turns_off (core : RSFCore) :
    GPUBuffer.isActive (RSFCore.gpu (disableGPU core)) = Bool.false := Eq.refl _

theorem disableGPU_preserves_dim (core : RSFCore) :
    RSFCore.dim (disableGPU core) = RSFCore.dim core := Eq.refl _

theorem disableGPU_preserves_layers (core : RSFCore) :
    RSFCore.layers (disableGPU core) = RSFCore.layers core := Eq.refl _

def invalidateGPUForMismatch (core : RSFCore) : RSFCore := disableGPU core

theorem invalidateGPUForMismatch_eq_disable (core : RSFCore) :
    invalidateGPUForMismatch core = disableGPU core := Eq.refl _

def layerGPUCompatible (layer : LayerCore) (cfg : RSFConfig) (dim : Nat) : Bool :=
  bAnd (natEqB (LayerCore.dim layer) dim)
    (FixedQ.eqB (LayerCore.clipMin layer) (RSFConfig.clipMin cfg))

theorem layerGPUCompatible_self (layer : LayerCore) :
    layerGPUCompatible layer
      (RSFConfig.mk (LayerCore.clipMin layer) (LayerCore.clipMax layer)
                    (LayerCore.gradMean layer) 1 1)
      (LayerCore.dim layer)
    = Bool.true :=
  let h_dim : natEqB (LayerCore.dim layer) (LayerCore.dim layer) = Bool.true :=
    natEqB_refl _
  let h_clip : FixedQ.eqB (LayerCore.clipMin layer) (LayerCore.clipMin layer) = Bool.true :=
    FixedQ.eqB_refl _
  Eq.trans
    (congrArg (fun x => bAnd x (FixedQ.eqB (LayerCore.clipMin layer) (LayerCore.clipMin layer))) h_dim)
    (Eq.trans (congrArg (fun x => bAnd Bool.true x) h_clip) (Eq.refl _))

def tensorClone (src : Tensor) : Tensor := src

theorem tensorClone_preserves_shape (t : Tensor) :
    Tensor.shape (tensorClone t) = Tensor.shape t := Eq.refl _

theorem tensorClone_preserves_dataLen (t : Tensor) :
    Tensor.dataLen (tensorClone t) = Tensor.dataLen t := Eq.refl _

theorem tensorClone_preserves_data (t : Tensor) :
    Tensor.data (tensorClone t) = Tensor.data t := Eq.refl _

def zeroTensor (t : Tensor) : Tensor :=
  Tensor.mk (Tensor.shape t) (List.replicate (Tensor.dataLen t) FixedQ.zero)

theorem zeroTensor_preserves_shape (t : Tensor) :
    Tensor.shape (zeroTensor t) = Tensor.shape t := Eq.refl _

theorem zeroTensor_dataLen (t : Tensor) :
    Tensor.dataLen (zeroTensor t) = Tensor.dataLen t :=
  List.length_replicate (Tensor.dataLen t) FixedQ.zero

def ensureFiniteSlice (data : List FixedQ) : ResultT Unit :=
  List.recOn (motive := fun _ => ResultT Unit) data
    (ResultT.ok Unit.unit)
    (fun h _ ih =>
      bIte (FixedQ.isFinite h)
        ih
        (ResultT.err ZigError.nonFinite))

theorem ensureFiniteSlice_nil :
    ensureFiniteSlice List.nil = ResultT.ok Unit.unit := Eq.refl _

theorem ensureFiniteSlice_cons_always_ok (h : FixedQ) (rest : List FixedQ) :
    ensureFiniteSlice (List.cons h rest) = ensureFiniteSlice rest :=
  let h_finite : FixedQ.isFinite h = Bool.true := Eq.refl Bool.true
  congrArg (fun c => bIte c (ensureFiniteSlice rest) (ResultT.err ZigError.nonFinite)) h_finite

theorem ensureFiniteSlice_always_ok (data : List FixedQ) :
    ensureFiniteSlice data = ResultT.ok Unit.unit :=
  List.recOn
    (motive := fun d => ensureFiniteSlice d = ResultT.ok Unit.unit)
    data
    (Eq.refl _)
    (fun h t ih =>
      Eq.trans (ensureFiniteSlice_cons_always_ok h t) ih)

def tensorsSameData (a b : Tensor) : Bool :=
  natEqB (Tensor.dataLen a) (Tensor.dataLen b)

theorem tensorsSameData_refl (t : Tensor) : tensorsSameData t t = Bool.true :=
  natEqB_refl _

def allocTensorArray (count rows cols : Nat) : List Tensor :=
  List.replicate count (Tensor.initZeros2D rows cols)

theorem allocTensorArray_length (count rows cols : Nat) :
    List.length (allocTensorArray count rows cols) = count :=
  List.length_replicate count (Tensor.initZeros2D rows cols)

def initRSFCore (dim numLayers : Nat) (cfg : RSFConfig) : ResultT RSFCore :=
  ResultT.bind (validateModelConfigValues dim numLayers cfg)
    (fun _ =>
      ResultT.bind (checkedMul dim dim)
        (fun _ =>
          ResultT.bind (checkedMul dim 2)
            (fun _ =>
              ResultT.ok
                (RSFCore.mk dim numLayers
                  (List.replicate numLayers
                    (LayerCore.mk
                      (Tensor.initZeros2D dim dim)
                      (Tensor.initZeros2D dim dim)
                      (Tensor.initZeros2D 1 dim)
                      (Tensor.initZeros2D 1 dim)
                      dim
                      (RSFConfig.clipMin cfg)
                      (RSFConfig.clipMax cfg)
                      (RSFConfig.gradMean cfg)))
                  cfg
                  GPUBuffer.disabled
                  0
                  1))))

theorem initRSFCore_ok_preserves_dim (dim numLayers : Nat) (cfg : RSFConfig) (c : RSFCore)
    (h : initRSFCore dim numLayers cfg = ResultT.ok c) :
    RSFCore.dim c = dim :=
  ResultT.recOn
    (motive := fun rv =>
      rv = validateModelConfigValues dim numLayers cfg →
      ResultT.bind rv (fun _ =>
        ResultT.bind (checkedMul dim dim) (fun _ =>
          ResultT.bind (checkedMul dim 2) (fun _ =>
            ResultT.ok
              (RSFCore.mk dim numLayers
                (List.replicate numLayers
                  (LayerCore.mk
                    (Tensor.initZeros2D dim dim)
                    (Tensor.initZeros2D dim dim)
                    (Tensor.initZeros2D 1 dim)
                    (Tensor.initZeros2D 1 dim)
                    dim
                    (RSFConfig.clipMin cfg)
                    (RSFConfig.clipMax cfg)
                    (RSFConfig.gradMean cfg)))
                cfg
                GPUBuffer.disabled
                0
                1)))) = ResultT.ok c →
      RSFCore.dim c = dim)
    (validateModelConfigValues dim numLayers cfg)
    (fun _ _ hv =>
      ResultT.recOn
        (motive := fun rv =>
          rv = checkedMul dim dim →
          ResultT.bind rv (fun _ =>
            ResultT.bind (checkedMul dim 2) (fun _ =>
              ResultT.ok
                (RSFCore.mk dim numLayers
                  (List.replicate numLayers
                    (LayerCore.mk
                      (Tensor.initZeros2D dim dim)
                      (Tensor.initZeros2D dim dim)
                      (Tensor.initZeros2D 1 dim)
                      (Tensor.initZeros2D 1 dim)
                      dim
                      (RSFConfig.clipMin cfg)
                      (RSFConfig.clipMax cfg)
                      (RSFConfig.gradMean cfg)))
                  cfg
                  GPUBuffer.disabled
                  0
                  1))) = ResultT.ok c →
          RSFCore.dim c = dim)
        (checkedMul dim dim)
        (fun _ _ hv2 =>
          ResultT.recOn
            (motive := fun rv =>
              rv = checkedMul dim 2 →
              ResultT.bind rv (fun _ => ResultT.ok
                (RSFCore.mk dim numLayers
                  (List.replicate numLayers
                    (LayerCore.mk
                      (Tensor.initZeros2D dim dim)
                      (Tensor.initZeros2D dim dim)
                      (Tensor.initZeros2D 1 dim)
                      (Tensor.initZeros2D 1 dim)
                      dim
                      (RSFConfig.clipMin cfg)
                      (RSFConfig.clipMax cfg)
                      (RSFConfig.gradMean cfg)))
                  cfg
                  GPUBuffer.disabled
                  0
                  1)) = ResultT.ok c →
              RSFCore.dim c = dim)
            (checkedMul dim 2)
            (fun _ _ hv3 =>
              let heq : RSFCore.mk dim numLayers
                  (List.replicate numLayers
                    (LayerCore.mk
                      (Tensor.initZeros2D dim dim)
                      (Tensor.initZeros2D dim dim)
                      (Tensor.initZeros2D 1 dim)
                      (Tensor.initZeros2D 1 dim)
                      dim
                      (RSFConfig.clipMin cfg)
                      (RSFConfig.clipMax cfg)
                      (RSFConfig.gradMean cfg)))
                  cfg
                  GPUBuffer.disabled
                  0
                  1 = c := ResultT.ok.inj hv3
              Eq.trans (Eq.symm (congrArg RSFCore.dim heq)) (Eq.refl dim))
            (fun _ _ hv3 => False.elim (ResultT.noConfusion hv3 (fun _ =>
              False.elim (boolFalseNeTrue (Eq.refl _)))))
            (Eq.refl _) hv2)
        (fun _ _ hv2 => False.elim (ResultT.noConfusion hv2 (fun _ =>
          False.elim (boolFalseNeTrue (Eq.refl _)))))
        (Eq.refl _) hv)
    (fun _ _ hv => False.elim (ResultT.noConfusion hv (fun _ =>
       False.elim (boolFalseNeTrue (Eq.refl _)))))
    (Eq.refl _) h

theorem registry_acquire_after_destroy (r : LayerRegistry) (id : Nat)
    (baseEntry : LayerRegistryEntry)
    (h : LayerRegistry.lookup r id = ResultT.ok baseEntry)
    (hd : LayerRegistryEntry.destroyed baseEntry = Bool.true)
    (hn : natEqB id 0 = Bool.false) :
    LayerRegistry.acquire r id = ResultT.err ZigError.notInitialized :=
  let step1 : LayerRegistry.acquire r id
              = ResultT.bind (LayerRegistry.lookup r id)
                (fun entry =>
                  bIte (LayerRegistryEntry.destroyed entry)
                    (ResultT.err ZigError.notInitialized)
                    (ResultT.ok (LayerRegistryEntry.mk (LayerRegistryEntry.core entry)
                                    (Nat.succ (LayerRegistryEntry.activeOps entry))
                                    Bool.false))) :=
    congrArg (fun c => bIte c (ResultT.err ZigError.notInitialized)
      (ResultT.bind (LayerRegistry.lookup r id)
        (fun entry =>
          bIte (LayerRegistryEntry.destroyed entry)
            (ResultT.err ZigError.notInitialized)
            (ResultT.ok (LayerRegistryEntry.mk (LayerRegistryEntry.core entry)
                            (Nat.succ (LayerRegistryEntry.activeOps entry))
                            Bool.false))))) hn
  let step2 : ResultT.bind (LayerRegistry.lookup r id)
                (fun entry =>
                  bIte (LayerRegistryEntry.destroyed entry)
                    (ResultT.err ZigError.notInitialized)
                    (ResultT.ok (LayerRegistryEntry.mk (LayerRegistryEntry.core entry)
                                    (Nat.succ (LayerRegistryEntry.activeOps entry))
                                    Bool.false)))
              = bIte (LayerRegistryEntry.destroyed baseEntry)
                    (ResultT.err ZigError.notInitialized)
                    (ResultT.ok (LayerRegistryEntry.mk (LayerRegistryEntry.core baseEntry)
                                    (Nat.succ (LayerRegistryEntry.activeOps baseEntry))
                                    Bool.false)) :=
    congrArg (fun rv => ResultT.bind rv
      (fun entry =>
        bIte (LayerRegistryEntry.destroyed entry)
          (ResultT.err ZigError.notInitialized)
          (ResultT.ok (LayerRegistryEntry.mk (LayerRegistryEntry.core entry)
                          (Nat.succ (LayerRegistryEntry.activeOps entry))
                          Bool.false)))) h
  let step3 : bIte (LayerRegistryEntry.destroyed baseEntry)
                   (ResultT.err ZigError.notInitialized)
                   (ResultT.ok (LayerRegistryEntry.mk (LayerRegistryEntry.core baseEntry)
                                   (Nat.succ (LayerRegistryEntry.activeOps baseEntry))
                                   Bool.false))
              = ResultT.err ZigError.notInitialized :=
    congrArg (fun c => bIte c (ResultT.err ZigError.notInitialized)
                              (ResultT.ok (LayerRegistryEntry.mk (LayerRegistryEntry.core baseEntry)
                                              (Nat.succ (LayerRegistryEntry.activeOps baseEntry))
                                              Bool.false))) hd
  Eq.trans step1 (Eq.trans step2 step3)

theorem bindLayerHandle_unused_slot_ok (id selfAddr : Nat) (hn : natEqB id 0 = Bool.false) :
    bindLayerHandle (RSFHandle.mk id) selfAddr HandleOwnerMap.empty = ResultT.ok id :=
  congrArg (fun c => bIte c (ResultT.err ZigError.notInitialized)
    (ResultT.recOn (motive := fun _ => ResultT Nat)
      (HandleOwnerMap.lookup HandleOwnerMap.empty id)
      (fun owner =>
        bIte (natEqB owner selfAddr)
          (ResultT.ok id)
          (ResultT.err ZigError.handleCopied))
      (fun _ => ResultT.ok id))) hn

def shouldDestroyLayerHandle (id selfAddr : Nat) (m : HandleOwnerMap) : Bool :=
  bIte (natEqB id 0) Bool.false
    (ResultT.recOn (motive := fun _ => Bool)
      (HandleOwnerMap.lookup m id)
      (fun owner => natEqB owner selfAddr)
      (fun _ => Bool.true))

theorem shouldDestroyLayerHandle_zero (selfAddr : Nat) (m : HandleOwnerMap) :
    shouldDestroyLayerHandle 0 selfAddr m = Bool.false := Eq.refl _

theorem shouldDestroyLayerHandle_empty (id selfAddr : Nat) (hn : natEqB id 0 = Bool.false) :
    shouldDestroyLayerHandle id selfAddr HandleOwnerMap.empty = Bool.true :=
  congrArg (fun c => bIte c Bool.false
    (ResultT.recOn (motive := fun _ => Bool)
      (HandleOwnerMap.lookup HandleOwnerMap.empty id)
      (fun owner => natEqB owner selfAddr)
      (fun _ => Bool.true))) hn

theorem forwardRow2D_yields_len (layer : LayerCore) (x1 x2 : List FixedQ)
    (h1 : List.length x1 = LayerCore.dim layer)
    (h2 : List.length x2 = LayerCore.dim layer) :
    List.length (forwardRow2D layer x1 x2)
    = Nat.add (LayerCore.dim layer) (LayerCore.dim layer) :=
  forwardRow2D_length layer x1 x2 h1 h2

theorem inverseRow2D_yields_len (layer : LayerCore) (y1 y2 : List FixedQ)
    (h1 : List.length y1 = LayerCore.dim layer)
    (h2 : List.length y2 = LayerCore.dim layer) :
    List.length (inverseRow2D layer y1 y2)
    = Nat.add (LayerCore.dim layer) (LayerCore.dim layer) :=
  inverseRow2D_length layer y1 y2 h1 h2

theorem zipWith_preserves_length_equal (f : FixedQ → FixedQ → FixedQ)
    (a b : List FixedQ) (n : Nat)
    (ha : List.length a = n) (hb : List.length b = n) :
    List.length (List.zipWith f a b) = n :=
  List.recOn
    (motive := fun x => (y : List FixedQ) →
      List.length x = n → List.length y = n →
      List.length (List.zipWith f x y) = n) a
    (fun _ hx _ => let e : n = 0 := Eq.symm hx; Eq.trans (Eq.refl 0) e)
    (fun ha' ta ih y =>
      List.recOn
        (motive := fun y =>
          List.length (List.cons ha' ta) = n → List.length y = n →
          List.length (List.zipWith f (List.cons ha' ta) y) = n) y
        (fun _ hy => let e : n = 0 := Eq.symm hy; Eq.trans (Eq.refl 0) e)
        (fun hb' tb _ hx hy =>
          let hxs : Nat.succ (List.length ta) = n := hx
          let hys : Nat.succ (List.length tb) = n := hy
          Nat.recOn
            (motive := fun d =>
              Nat.succ (List.length ta) = d →
              Nat.succ (List.length tb) = d →
              Nat.succ (List.length (List.zipWith f ta tb)) = d) n
            (fun h1 _ => False.elim (Nat.noConfusion h1))
            (fun d' _ ha'' hb'' =>
              let la : List.length ta = d' := Nat.succ.inj ha''
              let lb : List.length tb = d' := Nat.succ.inj hb''
              congrArg Nat.succ (ih tb la lb))
            hxs hys))
    b ha hb

def composeForwardBackward
    (_ : LayerCore) (_ _ : List FixedQ) (dy1 dy2 : List FixedQ) : List FixedQ :=
  zipWithAdd dy1 dy2

theorem composeForwardBackward_length
    (layer : LayerCore) (x1 x2 dy1 dy2 : List FixedQ) (n : Nat)
    (h1 : List.length dy1 = n) (h2 : List.length dy2 = n) :
    List.length (composeForwardBackward layer x1 x2 dy1 dy2) = n :=
  zipWithAdd_same_length dy1 dy2 n h1 h2

def chainRule
    (_ : LayerCore) (dy : List FixedQ) : List FixedQ :=
  List.map (fun q => FixedQ.mul q FixedQ.one) dy

theorem chainRule_preserves_length (layer : LayerCore) (dy : List FixedQ) :
    List.length (chainRule layer dy) = List.length dy :=
  List.recOn
    (motive := fun d => List.length (List.map (fun q => FixedQ.mul q FixedQ.one) d) = List.length d)
    dy
    (Eq.refl 0)
    (fun _ _ ih => congrArg Nat.succ ih)

def bOrAll (xs : List Bool) : Bool :=
  List.foldl bOr Bool.false xs

theorem bOrAll_nil : bOrAll List.nil = Bool.false := Eq.refl _

def bAndAll (xs : List Bool) : Bool :=
  List.foldl bAnd Bool.true xs

theorem bAndAll_nil : bAndAll List.nil = Bool.true := Eq.refl _

def lenEq (a b : List FixedQ) : Bool :=
  natEqB (List.length a) (List.length b)

theorem lenEq_refl (a : List FixedQ) : lenEq a a = Bool.true :=
  natEqB_refl _

theorem lenEq_symm (a b : List FixedQ) : lenEq a b = lenEq b a :=
  natEqB_symm _ _

def layerCoreSignature (l : LayerCore) : Nat :=
  Nat.add (LayerCore.dim l)
    (Nat.add (Tensor.dataLen (LayerCore.sWeight l))
      (Nat.add (Tensor.dataLen (LayerCore.tWeight l))
        (Nat.add (Tensor.dataLen (LayerCore.sBias l))
          (Tensor.dataLen (LayerCore.tBias l)))))

theorem forwardOnCore_layers_order (layers : List LayerCore) (x : Tensor) :
    forwardOnCore layers x
    = List.recOn
        (motive := fun _ => ResultT Tensor) layers
        (ResultT.ok x)
        (fun layer _ ih =>
          ResultT.bind ih (fun acc =>
            ResultT.bind (splitInto (LayerCore.dim layer) acc) (fun s1 =>
              ResultT.ok s1))) := Eq.refl _

theorem inverseOnCore_reverse_order (layers : List LayerCore) (y : Tensor) :
    inverseOnCore layers y
    = List.recOn
        (motive := fun _ => ResultT Tensor) (List.reverse layers)
        (ResultT.ok y)
        (fun layer _ ih =>
          ResultT.bind ih (fun acc =>
            ResultT.bind (splitInto (LayerCore.dim layer) acc) (fun s1 =>
              ResultT.ok s1))) := Eq.refl _

theorem empty_forward_inverse_id (x : Tensor) :
    ResultT.bind (forwardOnCore List.nil x)
      (fun y => inverseOnCore List.nil y) = ResultT.ok x :=
  Eq.refl _

theorem registry_insert_preserves_existing (r : LayerRegistry) (core : LayerCore) (id : Nat)
    (h : natEqB id (LayerRegistry.nextId r) = Bool.false) :
    LayerRegistry.lookup
      (LayerRegistry.insert r (LayerRegistry.register r core)) id
    = LayerRegistry.lookup r id :=
  let p := LayerRegistry.register r core
  let hp_id : RegEntryPair.id p = LayerRegistry.nextId r := Eq.refl _
  let newLookupUnfold : LayerRegistry.lookup
      (LayerRegistry.insert r p) id
    = bIte (natEqB (RegEntryPair.id p) id)
        (ResultT.ok (RegEntryPair.entry p))
        (LayerRegistry.lookup r id) := Eq.refl _
  let eqTrans : natEqB (RegEntryPair.id p) id = natEqB (LayerRegistry.nextId r) id :=
    congrArg (fun x => natEqB x id) hp_id
  let sy : natEqB (LayerRegistry.nextId r) id = natEqB id (LayerRegistry.nextId r) :=
    natEqB_symm _ _
  let hresult : natEqB (RegEntryPair.id p) id = Bool.false :=
    Eq.trans eqTrans (Eq.trans sy h)
  Eq.trans newLookupUnfold
    (congrArg (fun c => bIte c (ResultT.ok (RegEntryPair.entry p))
                              (LayerRegistry.lookup r id)) hresult)

theorem bindLayerHandle_bindsSelf (id selfAddr : Nat)
    (hn : natEqB id 0 = Bool.false) :
    bindLayerHandle (RSFHandle.mk id) selfAddr
      (HandleOwnerMap.insert HandleOwnerMap.empty id selfAddr)
    = ResultT.ok id :=
  let hlookup : HandleOwnerMap.lookup
      (HandleOwnerMap.insert HandleOwnerMap.empty id selfAddr) id
    = ResultT.ok selfAddr :=
    congrArg (fun c => bIte c (ResultT.ok selfAddr) (ResultT.err ZigError.notInitialized))
      (natEqB_refl id)
  let inner : ResultT.recOn (motive := fun _ => ResultT Nat)
      (HandleOwnerMap.lookup (HandleOwnerMap.insert HandleOwnerMap.empty id selfAddr) id)
      (fun owner =>
        bIte (natEqB owner selfAddr)
          (ResultT.ok id)
          (ResultT.err ZigError.handleCopied))
      (fun _ => ResultT.ok id)
    = bIte (natEqB selfAddr selfAddr)
        (ResultT.ok id)
        (ResultT.err ZigError.handleCopied) :=
    congrArg (fun rv => ResultT.recOn (motive := fun _ => ResultT Nat) rv
      (fun owner =>
        bIte (natEqB owner selfAddr)
          (ResultT.ok id)
          (ResultT.err ZigError.handleCopied))
      (fun _ => ResultT.ok id)) hlookup
  let inner2 : bIte (natEqB selfAddr selfAddr)
                (ResultT.ok id)
                (ResultT.err ZigError.handleCopied)
             = ResultT.ok id :=
    congrArg (fun c => bIte c (ResultT.ok id) (ResultT.err ZigError.handleCopied))
      (natEqB_refl selfAddr)
  let step1 : bindLayerHandle (RSFHandle.mk id) selfAddr
      (HandleOwnerMap.insert HandleOwnerMap.empty id selfAddr)
    = ResultT.recOn (motive := fun _ => ResultT Nat)
        (HandleOwnerMap.lookup (HandleOwnerMap.insert HandleOwnerMap.empty id selfAddr) id)
        (fun owner =>
          bIte (natEqB owner selfAddr)
            (ResultT.ok id)
            (ResultT.err ZigError.handleCopied))
        (fun _ => ResultT.ok id) :=
    congrArg (fun c => bIte c (ResultT.err ZigError.notInitialized)
      (ResultT.recOn (motive := fun _ => ResultT Nat)
        (HandleOwnerMap.lookup (HandleOwnerMap.insert HandleOwnerMap.empty id selfAddr) id)
        (fun owner =>
          bIte (natEqB owner selfAddr)
            (ResultT.ok id)
            (ResultT.err ZigError.handleCopied))
        (fun _ => ResultT.ok id))) hn
  Eq.trans step1 (Eq.trans inner inner2)

theorem bindLayerHandle_rejectsOtherOwner (id selfAddr otherAddr : Nat)
    (hn : natEqB id 0 = Bool.false)
    (hne : natEqB otherAddr selfAddr = Bool.false) :
    bindLayerHandle (RSFHandle.mk id) selfAddr
      (HandleOwnerMap.insert HandleOwnerMap.empty id otherAddr)
    = ResultT.err ZigError.handleCopied :=
  let hlookup : HandleOwnerMap.lookup
      (HandleOwnerMap.insert HandleOwnerMap.empty id otherAddr) id
    = ResultT.ok otherAddr :=
    congrArg (fun c => bIte c (ResultT.ok otherAddr) (ResultT.err ZigError.notInitialized))
      (natEqB_refl id)
  let inner : ResultT.recOn (motive := fun _ => ResultT Nat)
      (HandleOwnerMap.lookup (HandleOwnerMap.insert HandleOwnerMap.empty id otherAddr) id)
      (fun owner =>
        bIte (natEqB owner selfAddr)
          (ResultT.ok id)
          (ResultT.err ZigError.handleCopied))
      (fun _ => ResultT.ok id)
    = bIte (natEqB otherAddr selfAddr)
        (ResultT.ok id)
        (ResultT.err ZigError.handleCopied) :=
    congrArg (fun rv => ResultT.recOn (motive := fun _ => ResultT Nat) rv
      (fun owner =>
        bIte (natEqB owner selfAddr)
          (ResultT.ok id)
          (ResultT.err ZigError.handleCopied))
      (fun _ => ResultT.ok id)) hlookup
  let inner2 : bIte (natEqB otherAddr selfAddr)
                (ResultT.ok id)
                (ResultT.err ZigError.handleCopied)
             = ResultT.err ZigError.handleCopied :=
    congrArg (fun c => bIte c (ResultT.ok id) (ResultT.err ZigError.handleCopied)) hne
  let step : bindLayerHandle (RSFHandle.mk id) selfAddr
      (HandleOwnerMap.insert HandleOwnerMap.empty id otherAddr)
    = ResultT.recOn (motive := fun _ => ResultT Nat)
        (HandleOwnerMap.lookup (HandleOwnerMap.insert HandleOwnerMap.empty id otherAddr) id)
        (fun owner =>
          bIte (natEqB owner selfAddr)
            (ResultT.ok id)
            (ResultT.err ZigError.handleCopied))
        (fun _ => ResultT.ok id) :=
    congrArg (fun c => bIte c (ResultT.err ZigError.notInitialized)
      (ResultT.recOn (motive := fun _ => ResultT Nat)
        (HandleOwnerMap.lookup (HandleOwnerMap.insert HandleOwnerMap.empty id otherAddr) id)
        (fun owner =>
          bIte (natEqB owner selfAddr)
            (ResultT.ok id)
            (ResultT.err ZigError.handleCopied))
        (fun _ => ResultT.ok id))) hn
  Eq.trans step (Eq.trans inner inner2)

inductive HandleState : Type where
  | uninitialized : HandleState
  | initialized   : LayerCore → GradState → HandleState
  | copied        : HandleState

def HandleState.isValid (s : HandleState) : Bool :=
  HandleState.recOn (motive := fun _ => Bool) s
    Bool.false
    (fun _ _ => Bool.true)
    Bool.false

def acquireHandle (dim : Nat) (cfg : RSFLayerConfig) : ResultT HandleState :=
  ResultT.bind (LayerCore.initOwned dim cfg) (fun layer =>
    ResultT.ok (HandleState.initialized layer GradState.noGrad))

def releaseHandle (s : HandleState) : HandleState :=
  HandleState.recOn (motive := fun _ => HandleState) s
    HandleState.uninitialized
    (fun _ _ => HandleState.uninitialized)
    HandleState.uninitialized

def copyHandle (_ : HandleState) : HandleState :=
  HandleState.copied

theorem acquireHandle_ok_implies_dim_pos (dim : Nat) (cfg : RSFLayerConfig)
    (s : HandleState)
    (h : acquireHandle dim cfg = ResultT.ok s) :
    natEqB dim 0 = Bool.false :=
  let hLayerOk : Exists (fun (l : LayerCore) => LayerCore.initOwned dim cfg = ResultT.ok l) :=
    ResultT.recOn
      (motive := fun r =>
        ResultT.bind r (fun layer => ResultT.ok (HandleState.initialized layer GradState.noGrad))
        = ResultT.ok s →
        Exists (fun (l : LayerCore) => r = ResultT.ok l))
      (LayerCore.initOwned dim cfg)
      (fun l _ => Exists.intro l (Eq.refl _))
      (fun _ hk => False.elim (ResultT.noConfusion hk (fun _ => False.elim (boolFalseNeTrue (Eq.refl _)))))
      h
  Exists.elim hLayerOk (fun l hl =>
    LayerCore.initOwned_ok_implies_dim_pos dim cfg l hl)

theorem releaseHandle_always_invalid (s : HandleState) :
    HandleState.isValid (releaseHandle s) = Bool.false :=
  HandleState.recOn (motive := fun gs => HandleState.isValid (releaseHandle gs) = Bool.false)
    s
    (Eq.refl Bool.false)
    (fun _ _ => Eq.refl Bool.false)
    (Eq.refl Bool.false)

theorem copyHandle_always_copied (s : HandleState) :
    copyHandle s = HandleState.copied :=
  Eq.refl HandleState.copied

def simpleChecksum (data : List Nat) : Nat :=
  List.foldl Nat.add 0 data

def listNatOfFixedQ (xs : List FixedQ) : List Nat :=
  List.map (fun x =>
    FixedQ.recOn (motive := fun _ => Nat) x
      (fun n => n)
      (fun n => Nat.succ n)) xs

def modelChecksum (layers : List LayerCore) : Nat :=
  simpleChecksum
    (List.foldl
      (fun acc l =>
        List.append acc
          (listNatOfFixedQ
            (List.append (Tensor.data (LayerCore.sWeight l))
              (List.append (Tensor.data (LayerCore.tWeight l))
                (List.append (Tensor.data (LayerCore.sBias l))
                  (Tensor.data (LayerCore.tBias l)))))))
      List.nil layers)

theorem modelChecksum_nil :
    modelChecksum List.nil = 0 :=
  Eq.refl 0

theorem natAdd_zero (n : Nat) : Nat.add n 0 = n := Eq.refl n

theorem natZero_add (n : Nat) : Nat.add 0 n = n :=
  Nat.recOn (motive := fun m => Nat.add 0 m = m) n
    (Eq.refl 0)
    (fun m ih => congrArg Nat.succ ih)

theorem List.foldl_add_acc (ys : List Nat) (k : Nat) :
    List.foldl Nat.add k ys = Nat.add k (List.foldl Nat.add 0 ys) :=
  List.recOn
    (motive := fun l => (j : Nat) → List.foldl Nat.add j l = Nat.add j (List.foldl Nat.add 0 l))
    ys
    (fun j => Eq.refl j)
    (fun y yt ih j =>
      let lhs : List.foldl Nat.add j (List.cons y yt) = List.foldl Nat.add (Nat.add j y) yt :=
        Eq.refl _
      let lhsExp : List.foldl Nat.add (Nat.add j y) yt = Nat.add (Nat.add j y) (List.foldl Nat.add 0 yt) :=
        ih (Nat.add j y)
      let rhs : List.foldl Nat.add 0 (List.cons y yt) = List.foldl Nat.add y yt :=
        congrArg (fun w => List.foldl Nat.add w yt) (natZero_add y)
      let rhsExp : List.foldl Nat.add y yt = Nat.add y (List.foldl Nat.add 0 yt) := ih y
      let assoc : Nat.add (Nat.add j y) (List.foldl Nat.add 0 yt)
                = Nat.add j (Nat.add y (List.foldl Nat.add 0 yt)) :=
        Nat.recOn
          (motive := fun m =>
            Nat.add (Nat.add j y) m = Nat.add j (Nat.add y m))
          (List.foldl Nat.add 0 yt)
          (Eq.refl _)
          (fun m ih2 => congrArg Nat.succ ih2)
      Eq.trans lhs (Eq.trans lhsExp (Eq.trans assoc
        (congrArg (Nat.add j) (Eq.symm (Eq.trans rhs rhsExp)))))) k

theorem simpleChecksum_append (xs ys : List Nat) :
    simpleChecksum (List.append xs ys) =
    Nat.add (simpleChecksum xs) (simpleChecksum ys) :=
  List.recOn
    (motive := fun l =>
      simpleChecksum (List.append l ys) =
      Nat.add (simpleChecksum l) (simpleChecksum ys))
    xs
    (Eq.symm (natZero_add (simpleChecksum ys)))
    (fun x xt ih =>
      let lhs : simpleChecksum (List.append (List.cons x xt) ys)
              = List.foldl Nat.add 0 (List.cons x (List.append xt ys)) := Eq.refl _
      let lhs2 : List.foldl Nat.add 0 (List.cons x (List.append xt ys))
               = List.foldl Nat.add x (List.append xt ys) :=
        congrArg (fun w => List.foldl Nat.add w (List.append xt ys)) (natZero_add x)
      let lhs3 : List.foldl Nat.add x (List.append xt ys)
               = Nat.add x (List.foldl Nat.add 0 (List.append xt ys)) :=
        List.foldl_add_acc (List.append xt ys) x
      let rhsSimp : simpleChecksum (List.cons x xt) = Nat.add x (simpleChecksum xt) :=
        let s1 : simpleChecksum (List.cons x xt) = List.foldl Nat.add x xt :=
          congrArg (fun w => List.foldl Nat.add w xt) (natZero_add x)
        Eq.trans s1 (List.foldl_add_acc xt x)
      let assoc : Nat.add x (Nat.add (simpleChecksum xt) (simpleChecksum ys))
                = Nat.add (Nat.add x (simpleChecksum xt)) (simpleChecksum ys) :=
        Nat.recOn
          (motive := fun m =>
            Nat.add x (Nat.add m (simpleChecksum ys))
            = Nat.add (Nat.add x m) (simpleChecksum ys))
          (simpleChecksum xt)
          (Eq.refl _)
          (fun m ih2 => Eq.refl _)
      Eq.trans lhs (Eq.trans lhs2 (Eq.trans lhs3
        (Eq.trans (congrArg (Nat.add x) ih)
          (Eq.trans assoc
            (congrArg (fun w => Nat.add w (simpleChecksum ys)) (Eq.symm rhsSimp)))))))

end RSFLean
