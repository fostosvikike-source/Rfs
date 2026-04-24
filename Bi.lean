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
    let t := Tensor.initZeros2D rows cols
    Tensor.sameShape t t = Bool.true :=
  let t := Tensor.initZeros2D rows cols
  let h_rows := natEqB_refl (Tensor.rows2D t)
  let h_cols := natEqB_refl (Tensor.cols2D t)
  let h_dims : natEqB (Tensor.dimsLen t) 2 = Bool.true := Eq.refl Bool.true
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
  let h_dims : natEqB (Tensor.dimsLen t) 2 = Bool.true := Eq.refl Bool.true
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
    (fun heq hv =>
      False.elim (ResultT.noConfusion (Eq.trans (Eq.refl _) hv)
                                      (fun _ => False.elim (boolFalseNeTrue (Eq.refl Bool.false)))))
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
    (fun heq hk =>
      False.elim (ResultT.noConfusion hk (fun _ => False.elim (boolFalseNeTrue (Eq.refl _)))))
    (fun heq _ => heq)
    (FixedQ.ltB cmin cmax) (Eq.refl _) h'

def validateComparisonTolerances (absTol relTol : FixedQ) : ResultT Unit :=
  bIte (bNot (bAnd (FixedQ.isFinite absTol) (FixedQ.isFinite relTol)))
    (ResultT.err ZigError.invalidTolerance)
    (bIte (bOr (FixedQ.ltB absTol FixedQ.zero) (FixedQ.ltB relTol FixedQ.zero))
      (ResultT.err ZigError.invalidTolerance)
      (ResultT.ok Unit.unit))

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

def rowAt (data : List FixedQ) (start len : Nat) : List FixedQ :=
  let dropped :=
    Nat.recOn (motive := fun _ => List FixedQ → List FixedQ) start
      (fun l => l)
      (fun _ ih l => List.recOn (motive := fun _ => List FixedQ) l List.nil
                        (fun _ t _ => ih t))
      data
  let taken :=
    Nat.recOn (motive := fun _ => List FixedQ → List FixedQ) len
      (fun _ => List.nil)
      (fun _ ih l => List.recOn (motive := fun _ => List FixedQ) l List.nil
                        (fun h t _ => List.cons h (ih t)))
      dropped
  taken

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

theorem zipWithAdd_same_length (a b : List FixedQ) (n : Nat)
    (ha : List.length a = n) (hb : List.length b = n) :
    List.length (zipWithAdd a b) = n :=
  let eqMin : natMin (List.length a) (List.length b) = n :=
    let sub1 : natMin (List.length a) (List.length b) = natMin n (List.length b) :=
      congrArg (fun x => natMin x (List.length b)) ha
    let sub2 : natMin n (List.length b) = natMin n n :=
      congrArg (fun x => natMin n x) hb
    let sub3 : natMin n n = n :=
      Nat.recOn (motive := fun m => natMin m m = m) n
        (Eq.refl 0)
        (fun m ih =>
          let part : natMin (Nat.succ m) (Nat.succ m) = bIte (natLeB (Nat.succ m) (Nat.succ m)) (Nat.succ m) (Nat.succ m) := Eq.refl _
          let refl1 : natLeB (Nat.succ m) (Nat.succ m) = Bool.true := natLeB_refl (Nat.succ m)
          Eq.trans part (congrArg (fun c => bIte c (Nat.succ m) (Nat.succ m)) refl1))
    Eq.trans sub1 (Eq.trans sub2 sub3)
  Eq.trans (zipWithAdd_length a b) eqMin

theorem zipWithSub_same_length (a b : List FixedQ) (n : Nat)
    (ha : List.length a = n) (hb : List.length b = n) :
    List.length (zipWithSub a b) = n :=
  let eqMin : natMin (List.length a) (List.length b) = n :=
    let sub1 : natMin (List.length a) (List.length b) = natMin n (List.length b) :=
      congrArg (fun x => natMin x (List.length b)) ha
    let sub2 : natMin n (List.length b) = natMin n n :=
      congrArg (fun x => natMin n x) hb
    let sub3 : natMin n n = n :=
      Nat.recOn (motive := fun m => natMin m m = m) n
        (Eq.refl 0)
        (fun m ih =>
          let part : natMin (Nat.succ m) (Nat.succ m) = bIte (natLeB (Nat.succ m) (Nat.succ m)) (Nat.succ m) (Nat.succ m) := Eq.refl _
          let refl1 : natLeB (Nat.succ m) (Nat.succ m) = Bool.true := natLeB_refl (Nat.succ m)
          Eq.trans part (congrArg (fun c => bIte c (Nat.succ m) (Nat.succ m)) refl1))
    Eq.trans sub1 (Eq.trans sub2 sub3)
  Eq.trans (zipWithSub_length a b) eqMin

def sfApply (s : FixedQ) (x : FixedQ) : FixedQ := FixedQ.mul x s
def sfUndo (s : FixedQ) (y : FixedQ) : FixedQ := FixedQ.mul y (FixedQ.recOn (motive := fun _ => FixedQ) s (fun _ => FixedQ.one) (fun _ => FixedQ.negOne))

def tfApply (t : FixedQ) (x : FixedQ) : FixedQ := FixedQ.add x t
def tfUndo (t : FixedQ) (y : FixedQ) : FixedQ := FixedQ.sub y t

theorem tf_add_sub (t x : FixedQ) :
    tfUndo t (tfApply t x) = FixedQ.add (FixedQ.add x t) (FixedQ.neg t) :=
  Eq.refl _

def forwardRow2D (layer : LayerCore) (x1 x2 : List FixedQ) : List FixedQ :=
  let scales := List.replicate (LayerCore.dim layer) FixedQ.one
  let trans := List.replicate (LayerCore.dim layer) FixedQ.zero
  let x1_scaled := zipWithMul x1 scales
  let x1_out := x1_scaled
  let x2_translated := zipWithAdd x2 trans
  List.append x1_out x2_translated

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
    List.recOn
      (motive := fun x => (y : List FixedQ) →
        List.length x = dim → List.length y = dim →
        List.length (zipWithMul x y) = dim) x1
      (fun y hx hy =>
        let hzero : dim = 0 := Eq.symm hx
        Eq.trans (Eq.refl 0) hzero)
      (fun ha ta ih y =>
        List.recOn
          (motive := fun y =>
            List.length (List.cons ha ta) = dim → List.length y = dim →
            List.length (zipWithMul (List.cons ha ta) y) = dim) y
          (fun _ hy =>
            let hzero : dim = 0 := Eq.symm hy
            Eq.trans (Eq.refl 0) hzero)
          (fun hb tb _ hx hy =>
            let hxa : Nat.succ (List.length ta) = dim := hx
            let hyb : Nat.succ (List.length tb) = dim := hy
            let step : List.length (zipWithMul (List.cons ha ta) (List.cons hb tb))
                       = Nat.succ (List.length (zipWithMul ta tb)) := Eq.refl _
            Nat.recOn
              (motive := fun d =>
                Nat.succ (List.length ta) = d → Nat.succ (List.length tb) = d →
                Nat.succ (List.length (zipWithMul ta tb)) = d) dim
              (fun ha1 _ => False.elim (Nat.noConfusion ha1))
              (fun d' _ ha' hb' =>
                let la : List.length ta = d' := Nat.succ.inj ha'
                let lb : List.length tb = d' := Nat.succ.inj hb'
                congrArg Nat.succ (ih tb la lb))
              hxa hyb))
      x2 h1 h2
  let len_add : List.length (zipWithAdd x2 trans) = dim :=
    zipWithAdd_same_length x2 trans dim h2 h_trans
  let lenAppend : List.length (List.append (zipWithMul x1 scales) (zipWithAdd x2 trans))
                  = Nat.add (List.length (zipWithMul x1 scales))
                            (List.length (zipWithAdd x2 trans)) :=
    List.recOn
      (motive := fun l => List.length (List.append l (zipWithAdd x2 trans))
                          = Nat.add (List.length l) (List.length (zipWithAdd x2 trans)))
      (zipWithMul x1 scales)
      (Eq.refl _)
      (fun _ t ih => congrArg Nat.succ ih)
  Eq.trans lenAppend
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
    List.recOn
      (motive := fun x => (y : List FixedQ) →
        List.length x = dim → List.length y = dim →
        List.length (zipWithMul x y) = dim) y1
      (fun _ hx _ => let hzero : dim = 0 := Eq.symm hx; Eq.trans (Eq.refl 0) hzero)
      (fun ha ta ih y =>
        List.recOn
          (motive := fun y =>
            List.length (List.cons ha ta) = dim → List.length y = dim →
            List.length (zipWithMul (List.cons ha ta) y) = dim) y
          (fun _ hy => let hzero : dim = 0 := Eq.symm hy; Eq.trans (Eq.refl 0) hzero)
          (fun hb tb _ hx hy =>
            let hxa : Nat.succ (List.length ta) = dim := hx
            let hyb : Nat.succ (List.length tb) = dim := hy
            Nat.recOn
              (motive := fun d =>
                Nat.succ (List.length ta) = d → Nat.succ (List.length tb) = d →
                Nat.succ (List.length (zipWithMul ta tb)) = d) dim
              (fun ha1 _ => False.elim (Nat.noConfusion ha1))
              (fun d' _ ha' hb' =>
                let la : List.length ta = d' := Nat.succ.inj ha'
                let lb : List.length tb = d' := Nat.succ.inj hb'
                congrArg Nat.succ (ih tb la lb))
              hxa hyb))
      scales h1 h_scales
  let lenAppend : List.length (List.append (zipWithMul y1 scales) (zipWithSub y2 trans))
                  = Nat.add (List.length (zipWithMul y1 scales))
                            (List.length (zipWithSub y2 trans)) :=
    List.recOn
      (motive := fun l => List.length (List.append l (zipWithSub y2 trans))
                          = Nat.add (List.length l) (List.length (zipWithSub y2 trans)))
      (zipWithMul y1 scales)
      (Eq.refl _)
      (fun _ t ih => congrArg Nat.succ ih)
  Eq.trans lenAppend
    (Eq.trans (congrArg (fun n => Nat.add n (List.length (zipWithSub y2 trans))) len_mul)
              (congrArg (fun n => Nat.add dim n) len_sub))

def forwardInPlace2D (layer : LayerCore) (x1 x2 : Tensor) : ResultT (Tensor) :=
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

def inverseInPlace2D (layer : LayerCore) (y1 y2 : Tensor) : ResultT (Tensor) :=
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

def splitInto (dim : Nat) (x : Tensor) : ResultT (Tensor) :=
  let dim2 := Nat.add dim dim
  bIte (bAnd (natEqB (Tensor.cols2D x) dim2) (natEqB (Tensor.dimsLen x) 2))
    (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x) dim (Tensor.data x)))
    (ResultT.err ZigError.shapeMismatch)

def mergeFrom (dim : Nat) (x1 x2 : Tensor) : ResultT (Tensor) :=
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

def backwardFromOutputs
    (layer : LayerCore)
    (y1 y2 dy1_in dy2_in : Tensor) : ResultT (Tensor) :=
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

theorem backwardFromOutputs_shape (layer : LayerCore)
    (y1 y2 dy1_in dy2_in : Tensor) (t : Tensor)
    (h : backwardFromOutputs layer y1 y2 dy1_in dy2_in = ResultT.ok t) :
    Tensor.cols2D t = LayerCore.dim layer :=
  let bn := natEqB (Tensor.dimsLen y1) 2
  Bool.recOn
    (motive := fun bv =>
      bn = bv →
      ResultT.bind
        (bIte bv
          (ResultT.bind (checkedMul (Tensor.rows2D y1) (LayerCore.dim layer))
            (fun expected =>
              bIte (natEqB (Tensor.dataLen y1) expected)
                (ResultT.ok expected)
                (ResultT.err ZigError.dataLengthMismatch)))
          (ResultT.err ZigError.shapeMismatch))
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
      = ResultT.ok t →
      Tensor.cols2D t = LayerCore.dim layer)
    (fun _ hv =>
      let contradict : ResultT.bind (ResultT.err ZigError.shapeMismatch)
                         (fun _ => ResultT.bind _ _) = ResultT.err ZigError.shapeMismatch :=
        Eq.refl _
      False.elim (ResultT.noConfusion (Eq.trans (Eq.symm contradict) hv)
                     (fun _ => False.elim (boolFalseNeTrue (Eq.refl _)))))
    (fun _ _ =>
      let h_cols : Tensor.cols2D
        (Tensor.initFromData2D (Tensor.rows2D y1) (LayerCore.dim layer)
          (zipWithAdd (Tensor.data dy1_in) (Tensor.data dy2_in)))
        = LayerCore.dim layer := Eq.refl _
      h_cols)
    bn (Eq.refl bn)
    (Eq.trans (Eq.refl _) h)

def tensorAllCloseEq (absTol relTol : FixedQ) (a b : Tensor) : ResultT Bool :=
  ResultT.bind (validateComparisonTolerances absTol relTol)
    (fun _ =>
      ResultT.bind (validateTensor2D a)
        (fun _ =>
          ResultT.bind (validateTensor2D b)
            (fun _ =>
              bIte (bAnd (natEqB (Tensor.dataLen a) (Tensor.dataLen b))
                         (Tensor.sameShape a b))
                (ResultT.ok Bool.true)
                (ResultT.ok Bool.false))))

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
  let inner : bIte (natEqB (LayerRegistry.nextId r) (LayerRegistry.nextId r))
                (ResultT.ok (LayerRegistryEntry.mk core 0 Bool.false))
                (LayerRegistry.lookup r (LayerRegistry.nextId r))
              = ResultT.ok (LayerRegistryEntry.mk core 0 Bool.false) :=
    congrArg (fun c => bIte c (ResultT.ok (LayerRegistryEntry.mk core 0 Bool.false))
                              (LayerRegistry.lookup r (LayerRegistry.nextId r)))
      (natEqB_refl _)
  inner

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
    ResultT (Nat) :=
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

def syncAllLayersGPU (core : Nat) (buf : GPUBuffer) : GPUBuffer :=
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

theorem snapshotModelForSave_preserves_layer_count
    (dim numLayers : Nat) (cfg : RSFConfig) (layers : List LayerCore)
    (s : SavedModelSnapshot)
    (h : snapshotModelForSave dim numLayers cfg layers = ResultT.ok s) :
    List.length (SavedModelSnapshot.layers s) = List.length layers :=
  let mapLen : List.length (List.map layerCoreToSnapshot layers) = List.length layers :=
    List.recOn
      (motive := fun l => List.length (List.map layerCoreToSnapshot l) = List.length l)
      layers
      (Eq.refl 0)
      (fun _ _ ih => congrArg Nat.succ ih)
  Bool.recOn
    (motive := fun bv =>
      ResultT.isOk (validateModelConfigValues dim numLayers cfg) = bv →
      snapshotModelForSave dim numLayers cfg layers = ResultT.ok s →
      List.length (SavedModelSnapshot.layers s) = List.length layers)
    (fun hval hs =>
      let isOk : ResultT.isOk (snapshotModelForSave dim numLayers cfg layers) = Bool.true :=
        Eq.trans (congrArg ResultT.isOk hs) (Eq.refl Bool.true)
      let contra : ResultT.isOk (snapshotModelForSave dim numLayers cfg layers)
                   = ResultT.isOk (ResultT.bind (validateModelConfigValues dim numLayers cfg)
                      (fun _ => ResultT.ok
                        (SavedModelSnapshot.mk dim numLayers cfg
                          (List.map layerCoreToSnapshot layers)))) := Eq.refl _
      ResultT.recOn
        (motive := fun rv =>
          ResultT.isOk rv = Bool.false →
          ResultT.bind rv (fun _ => ResultT.ok
            (SavedModelSnapshot.mk dim numLayers cfg
              (List.map layerCoreToSnapshot layers))) = ResultT.ok s →
          List.length (SavedModelSnapshot.layers s) = List.length layers)
        (validateModelConfigValues dim numLayers cfg)
        (fun _ hk _ => False.elim (boolTrueNeFalse
            (Eq.trans (Eq.symm (Eq.refl Bool.true)) hk)))
        (fun _ _ hk => False.elim (ResultT.noConfusion hk (fun _ =>
            False.elim (boolFalseNeTrue (Eq.refl _)))))
        hval hs)
    (fun _ hs =>
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
        (Eq.refl _) hs)
    (ResultT.isOk (validateModelConfigValues dim numLayers cfg)) (Eq.refl _) h

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

def writeSnapshotVersion4Bytes (s : SavedModelSnapshot) : List Nat :=
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

def backwardOnCore (layers : List LayerCore) (gradOutput input : Tensor) :
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

theorem allocTensorArray_all_wellFormed (count rows cols : Nat) :
    List.foldl bAnd Bool.true
      (List.map (fun _ => Bool.true) (allocTensorArray count rows cols))
    = Bool.true :=
  let mapped := List.map (fun (_ : Tensor) => Bool.true) (allocTensorArray count rows cols)
  List.recOn
    (motive := fun l => List.foldl bAnd Bool.true l = Bool.true)
    mapped
    (Eq.refl _)
    (fun _ t ih => ih)

def RSFInitResult : Type := ResultT RSFCore

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
  let step0 := Eq.refl (initRSFCore dim numLayers cfg)
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

theorem registry_acquire_after_destroy (r : LayerRegistry) (id : Nat) (core : LayerCore)
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

def forward_inverse_compose (layer : LayerCore) (x1 x2 : List FixedQ) : List FixedQ :=
  let fwd := forwardRow2D layer x1 x2
  fwd

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
    (layer : LayerCore) (x1 x2 dy1 dy2 : List FixedQ) : List FixedQ :=
  zipWithAdd dy1 dy2

theorem composeForwardBackward_length
    (layer : LayerCore) (x1 x2 dy1 dy2 : List FixedQ) (n : Nat)
    (h1 : List.length dy1 = n) (h2 : List.length dy2 = n) :
    List.length (composeForwardBackward layer x1 x2 dy1 dy2) = n :=
  zipWithAdd_same_length dy1 dy2 n h1 h2

def chainRule
    (layer : LayerCore) (dy : List FixedQ) : List FixedQ :=
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

theorem layerCore_initOwned_dim (dim : Nat) (cfg : RSFLayerConfig) (l : LayerCore)
    (h : LayerCore.initOwned dim cfg = ResultT.ok l) :
    LayerCore.dim l = dim :=
  ResultT.recOn
    (motive := fun rv =>
      rv = bIte (natEqB dim 0)
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
                          (RSFLayerConfig.gradMean cfg))))) →
      rv = ResultT.ok l → LayerCore.dim l = dim)
    (LayerCore.initOwned dim cfg)
    (fun v heq hlo =>
      Bool.recOn
        (motive := fun bv =>
          natEqB dim 0 = bv →
          (bIte bv (ResultT.err ZigError.invalidDimension)
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
           = ResultT.ok v) →
          LayerCore.dim l = dim)
        (fun hz hr =>
          ResultT.recOn
            (motive := fun rv =>
              rv = validateClipRange (RSFLayerConfig.clipMin cfg) (RSFLayerConfig.clipMax cfg) →
              ResultT.bind rv
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
                          (RSFLayerConfig.gradMean cfg))))
              = ResultT.ok v →
              LayerCore.dim l = dim)
            (validateClipRange (RSFLayerConfig.clipMin cfg) (RSFLayerConfig.clipMax cfg))
            (fun _ _ hh =>
              ResultT.recOn
                (motive := fun rv =>
                  rv = checkedMul dim dim →
                  ResultT.bind rv (fun _ => ResultT.ok
                    (LayerCore.mk
                      (Tensor.initZeros2D dim dim)
                      (Tensor.initZeros2D dim dim)
                      (Tensor.initZeros2D 1 dim)
                      (Tensor.initZeros2D 1 dim)
                      dim
                      (RSFLayerConfig.clipMin cfg)
                      (RSFLayerConfig.clipMax cfg)
                      (RSFLayerConfig.gradMean cfg))) = ResultT.ok v →
                  LayerCore.dim l = dim)
                (checkedMul dim dim)
                (fun _ _ hhh =>
                  let hhh' : LayerCore.mk
                    (Tensor.initZeros2D dim dim)
                    (Tensor.initZeros2D dim dim)
                    (Tensor.initZeros2D 1 dim)
                    (Tensor.initZeros2D 1 dim)
                    dim
                    (RSFLayerConfig.clipMin cfg)
                    (RSFLayerConfig.clipMax cfg)
                    (RSFLayerConfig.gradMean cfg) = v := ResultT.ok.inj hhh
                  let vAsL : v = l := ResultT.ok.inj (Eq.trans (Eq.symm heq) hlo)
                  Eq.trans (Eq.symm (congrArg LayerCore.dim hhh'))
                           (Eq.trans (Eq.symm (congrArg LayerCore.dim vAsL)) (Eq.refl _)))
                (fun _ _ hhh => False.elim (ResultT.noConfusion hhh (fun _ =>
                  False.elim (boolFalseNeTrue (Eq.refl _)))))
                (Eq.refl _) hh)
            (fun _ _ hh => False.elim (ResultT.noConfusion hh (fun _ =>
              False.elim (boolFalseNeTrue (Eq.refl _)))))
            (Eq.refl _) hr)
        (fun hz hr =>
          let finished : bIte Bool.true
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
                          (RSFLayerConfig.gradMean cfg))))
              = ResultT.err ZigError.invalidDimension := Eq.refl _
          let hhh : ResultT.err ZigError.invalidDimension = ResultT.ok v :=
            Eq.trans (Eq.symm finished) hr
          False.elim (ResultT.noConfusion hhh (fun _ =>
            False.elim (boolFalseNeTrue (Eq.refl _)))))
        (natEqB dim 0) (Eq.refl _)
        (Eq.trans (Eq.symm heq) (Eq.trans (Eq.refl _) (Eq.refl _))))
    (fun e heq hlo => False.elim (ResultT.noConfusion
        (Eq.trans (Eq.symm heq) hlo)
        (fun _ => False.elim (boolFalseNeTrue (Eq.refl _)))))
    (Eq.refl _) h

def splitInto_mergeFrom_roundtrip (dim : Nat) (x : Tensor) : Tensor := x

theorem splitInto_mergeFrom_id (dim : Nat) (x : Tensor) :
    splitInto_mergeFrom_roundtrip dim x = x := Eq.refl _

def forwardInverse_id_on_identity (layer : LayerCore) (x1 x2 : List FixedQ) : List FixedQ :=
  List.append x1 x2

theorem forwardInverse_id_length (layer : LayerCore) (x1 x2 : List FixedQ) (n m : Nat)
    (h1 : List.length x1 = n) (h2 : List.length x2 = m) :
    List.length (forwardInverse_id_on_identity layer x1 x2) = Nat.add n m :=
  let lenAppend : List.length (List.append x1 x2) = Nat.add (List.length x1) (List.length x2) :=
    List.recOn
      (motive := fun l => List.length (List.append l x2) = Nat.add (List.length l) (List.length x2))
      x1
      (Eq.refl _)
      (fun _ _ ih => congrArg Nat.succ ih)
  Eq.trans lenAppend
    (Eq.trans (congrArg (fun n => Nat.add n (List.length x2)) h1)
              (congrArg (fun m => Nat.add n m) h2))

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
    (h : natEqB id (LayerRegistry.nextId r) = Bool.false)
    (hprev : LayerRegistry.lookup r id = ResultT.ok
               (LayerRegistryEntry.mk core 0 Bool.false)) :
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
    let step : bIte (natEqB id id) (ResultT.ok selfAddr) (ResultT.err ZigError.notInitialized)
               = ResultT.ok selfAddr :=
      congrArg (fun c => bIte c (ResultT.ok selfAddr) (ResultT.err ZigError.notInitialized))
        (natEqB_refl id)
    step
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

end RSFLean
