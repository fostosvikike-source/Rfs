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

theorem ResultT.ok_ne_err {α : Type} {v : α} {e : ZigError}
    (h : ResultT.ok v = ResultT.err e) : False :=
  Eq.mp
    (congrArg (fun r =>
      ResultT.recOn (motive := fun _ => Prop) r (fun _ => True) (fun _ => False)) h)
    True.intro

theorem ResultT.err_ne_ok {α : Type} {e : ZigError} {v : α}
    (h : ResultT.err e = ResultT.ok v) : False :=
  ResultT.ok_ne_err (Eq.symm h)

theorem ResultT.ok_inj {α : Type} {a b : α}
    (h : ResultT.ok a = ResultT.ok b) : a = b :=
  congrArg (fun r =>
    ResultT.recOn (motive := fun _ => α) r (fun v => v) (fun _ => a)) h

theorem ResultT.err_inj {α : Type} {e1 e2 : ZigError}
    (h : ResultT.err e1 = ResultT.err e2) : e1 = e2 :=
  congrArg (fun r =>
    ResultT.recOn (motive := fun _ => ZigError) r (fun _ => e1) (fun e => e)) h

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

def bNot (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) Bool.true Bool.false b

def bAnd (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) Bool.false b a

def bOr (a b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) b Bool.true a

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

theorem bOr_false_l (b : Bool) : bOr Bool.false b = b := Eq.refl b
theorem bOr_true_l (b : Bool) : bOr Bool.true b = Bool.true := Eq.refl Bool.true

theorem bOr_false_r (b : Bool) : bOr b Bool.false = b :=
  Bool.rec (motive := fun x => bOr x Bool.false = x)
    (Eq.refl Bool.false) (Eq.refl Bool.true) b

theorem bOr_true_r (b : Bool) : bOr b Bool.true = Bool.true :=
  Bool.rec (motive := fun x => bOr x Bool.true = Bool.true)
    (Eq.refl Bool.true) (Eq.refl Bool.true) b

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

theorem natEqB_refl (n : Nat) : natEqB n n = Bool.true :=
  Nat.recOn (motive := fun m => natEqB m m = Bool.true) n
    (Eq.refl Bool.true)
    (fun _ ih => ih)

theorem natLeB_refl (n : Nat) : natLeB n n = Bool.true :=
  Nat.recOn (motive := fun m => natLeB m m = Bool.true) n
    (Eq.refl Bool.true)
    (fun _ ih => ih)

theorem natLeB_zero (n : Nat) : natLeB 0 n = Bool.true := Eq.refl Bool.true

theorem natSuccInj {m n : Nat} (h : Nat.succ m = Nat.succ n) : m = n :=
  congrArg natPred h

theorem natSuccNe0 {n : Nat} (h : Nat.succ n = 0) : False :=
  Eq.mp
    (congrArg (fun m => Nat.recOn (motive := fun _ => Prop) m False (fun _ _ => True)) h)
    True.intro

theorem nat0NeSucc {n : Nat} (h : 0 = Nat.succ n) : False :=
  natSuccNe0 (Eq.symm h)

theorem natMin_same (n : Nat) : natMin n n = n :=
  congrArg (fun c => bIte c n n) (natLeB_refl n)

theorem natAdd_zero_r (n : Nat) : Nat.add n 0 = n := Eq.refl n

theorem natAdd_succ_r (n m : Nat) : Nat.add n (Nat.succ m) = Nat.succ (Nat.add n m) :=
  Eq.refl _

inductive FixedQ : Type where
  | nonneg : Nat → FixedQ
  | negsucc : Nat → FixedQ

def FixedQ.zero : FixedQ := FixedQ.nonneg 0
def FixedQ.one : FixedQ := FixedQ.nonneg 1
def FixedQ.negOne : FixedQ := FixedQ.negsucc 0

def FixedQ.neg (x : FixedQ) : FixedQ :=
  FixedQ.recOn (motive := fun _ => FixedQ) x
    (fun n =>
      Nat.recOn (motive := fun _ => FixedQ) n
        (FixedQ.nonneg 0)
        (fun n' _ => FixedQ.negsucc n'))
    (fun n => FixedQ.nonneg (Nat.succ n))

def FixedQ.isFinite (_ : FixedQ) : Bool := Bool.true

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
      Eq.trans step1 (congrArg (fun k => FixedQ.neg (FixedQ.nonneg k)) lem))

def maxUsize : Nat := 18446744073709551615

def checkedMul (a b : Nat) : ResultT Nat :=
  bIte (natLeB (Nat.mul a b) maxUsize)
    (ResultT.ok (Nat.mul a b))
    (ResultT.err ZigError.overflow)

def checkedAdd (a b : Nat) : ResultT Nat :=
  bIte (natLeB (Nat.add a b) maxUsize)
    (ResultT.ok (Nat.add a b))
    (ResultT.err ZigError.overflow)

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

theorem checkedMul_ok_implies_bound (a b : Nat) (n : Nat)
    (h : checkedMul a b = ResultT.ok n) :
    natLeB (Nat.mul a b) maxUsize = Bool.true :=
  Bool.recOn
    (motive := fun bv =>
      natLeB (Nat.mul a b) maxUsize = bv →
      bIte bv (ResultT.ok (Nat.mul a b)) (ResultT.err ZigError.overflow) = ResultT.ok n →
      natLeB (Nat.mul a b) maxUsize = Bool.true)
    (fun _ hv => False.elim (ResultT.err_ne_ok hv))
    (fun heq _ => Eq.symm heq)
    (natLeB (Nat.mul a b) maxUsize) (Eq.refl _) h

theorem checkedMul_ok_implies_value (a b : Nat) (n : Nat)
    (h : checkedMul a b = ResultT.ok n) :
    n = Nat.mul a b :=
  let hbound := checkedMul_ok_implies_bound a b n h
  let heq : checkedMul a b = ResultT.ok (Nat.mul a b) := checkedMul_ok_of_bound a b hbound
  ResultT.ok_inj (Eq.trans (Eq.symm heq) h)

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

def Tensor.initZeros2D (rows cols : Nat) : Tensor :=
  Tensor.mk (Shape.mk2D rows cols) (List.replicate (Nat.mul rows cols) FixedQ.zero)

theorem Tensor.initZeros2D_dataLen (rows cols : Nat) :
    Tensor.dataLen (Tensor.initZeros2D rows cols) = Nat.mul rows cols :=
  List.length_replicate (Nat.mul rows cols) FixedQ.zero

theorem Tensor.initZeros2D_rows (rows cols : Nat) :
    Tensor.rows2D (Tensor.initZeros2D rows cols) = rows := Eq.refl rows

theorem Tensor.initZeros2D_cols (rows cols : Nat) :
    Tensor.cols2D (Tensor.initZeros2D rows cols) = cols := Eq.refl cols

def Tensor.initFromData2D (rows cols : Nat) (d : List FixedQ) : Tensor :=
  Tensor.mk (Shape.mk2D rows cols) d

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

def Tensor.sameShape (a b : Tensor) : Bool :=
  bAnd (natEqB (Tensor.dimsLen a) 2)
    (bAnd (natEqB (Tensor.dimsLen b) 2)
      (bAnd (natEqB (Tensor.rows2D a) (Tensor.rows2D b))
            (natEqB (Tensor.cols2D a) (Tensor.cols2D b))))

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

theorem tensorsOverlap_empty_left (a b : AddrTensor)
    (h : natEqB (Tensor.dataLen (AddrTensor.tensor a)) 0 = Bool.true) :
    tensorsOverlap a b = Bool.false :=
  let hOr : bOr (natEqB (Tensor.dataLen (AddrTensor.tensor a)) 0)
                (natEqB (Tensor.dataLen (AddrTensor.tensor b)) 0) = Bool.true :=
    Eq.trans (congrArg (fun x => bOr x (natEqB (Tensor.dataLen (AddrTensor.tensor b)) 0)) h)
             (bOr_true_l _)
  congrArg (fun c => bIte c Bool.false
                       (bAnd (natLtB (tensorStart a) (tensorEnd b))
                             (natLtB (tensorStart b) (tensorEnd a)))) hOr

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

def copyTensorPairInto (out1 out2 _in1 _in2 : AddrTensor) : ResultT Unit :=
  bIte (tensorsOverlap out1 out2)
    (ResultT.err ZigError.aliasedBuffers)
    (ResultT.ok Unit.unit)

theorem copyTensorPairInto_noAlias (a b : AddrTensor)
    (h : tensorsOverlap a b = Bool.false) :
    copyTensorPairInto a b a b = ResultT.ok Unit.unit :=
  congrArg (fun c => bIte c (ResultT.err ZigError.aliasedBuffers) (ResultT.ok Unit.unit)) h

theorem copyTensorPairInto_alias_err (a b : AddrTensor)
    (h : tensorsOverlap a b = Bool.true) :
    copyTensorPairInto a b a b = ResultT.err ZigError.aliasedBuffers :=
  congrArg (fun c => bIte c (ResultT.err ZigError.aliasedBuffers) (ResultT.ok Unit.unit)) h

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
  Eq.refl Bool.false

theorem validateClipRange_implies_ordered (cmin cmax : FixedQ)
    (h : validateClipRange cmin cmax = ResultT.ok Unit.unit) :
    FixedQ.ltB cmin cmax = Bool.true :=
  let h' :
      bIte (bNot (FixedQ.ltB cmin cmax))
        (ResultT.err ZigError.invalidConfig)
        (bIte (bOr (FixedQ.ltB (FixedQ.nonneg 20) cmax)
                   (FixedQ.ltB cmin (FixedQ.negsucc 19)))
          (ResultT.err ZigError.invalidConfig)
          (ResultT.ok Unit.unit))
      = ResultT.ok Unit.unit := h
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
    (fun _ hk => False.elim (ResultT.err_ne_ok hk))
    (fun heq _ => heq)
    (FixedQ.ltB cmin cmax) (Eq.refl _) h'

def validateComparisonTolerances (absTol relTol : FixedQ) : ResultT Unit :=
  bIte (bNot (bAnd (FixedQ.isFinite absTol) (FixedQ.isFinite relTol)))
    (ResultT.err ZigError.invalidTolerance)
    (bIte (bOr (FixedQ.ltB absTol FixedQ.zero) (FixedQ.ltB relTol FixedQ.zero))
      (ResultT.err ZigError.invalidTolerance)
      (ResultT.ok Unit.unit))

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
    (fun _ hv => False.elim (ResultT.err_ne_ok hv))
    (natEqB dim 0) (Eq.refl _) h

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
    (fun _ hv => False.elim (ResultT.err_ne_ok hv))
    (natEqB dim 0) (Eq.refl _) h

def zipWithAdd (a b : List FixedQ) : List FixedQ := List.zipWith FixedQ.add a b
def zipWithSub (a b : List FixedQ) : List FixedQ := List.zipWith FixedQ.sub a b
def zipWithMul (a b : List FixedQ) : List FixedQ := List.zipWith FixedQ.mul a b

theorem zipWith_same_length (f : FixedQ → FixedQ → FixedQ)
    (a b : List FixedQ) (n : Nat)
    (ha : List.length a = n) (hb : List.length b = n) :
    List.length (List.zipWith f a b) = n :=
  List.recOn
    (motive := fun x => (y : List FixedQ) →
      List.length x = n → List.length y = n →
      List.length (List.zipWith f x y) = n) a
    (fun _ hx _ => Eq.symm hx)
    (fun ha' ta ih y =>
      List.recOn
        (motive := fun y =>
          List.length (List.cons ha' ta) = n → List.length y = n →
          List.length (List.zipWith f (List.cons ha' ta) y) = n) y
        (fun _ hy => Eq.symm hy)
        (fun _ tb _ hx hy =>
          let hxs : Nat.succ (List.length ta) = n := hx
          let hys : Nat.succ (List.length tb) = n := hy
          Nat.recOn
            (motive := fun d =>
              Nat.succ (List.length ta) = d →
              Nat.succ (List.length tb) = d →
              Nat.succ (List.length (List.zipWith f ta tb)) = d) n
            (fun h1 _ => False.elim (natSuccNe0 h1))
            (fun d' _ ha'' hb'' =>
              let la : List.length ta = d' := natSuccInj ha''
              let lb : List.length tb = d' := natSuccInj hb''
              congrArg Nat.succ (ih tb la lb))
            hxs hys))
    b ha hb

theorem zipWithAdd_same_length (a b : List FixedQ) (n : Nat)
    (ha : List.length a = n) (hb : List.length b = n) :
    List.length (zipWithAdd a b) = n := zipWith_same_length FixedQ.add a b n ha hb

theorem zipWithSub_same_length (a b : List FixedQ) (n : Nat)
    (ha : List.length a = n) (hb : List.length b = n) :
    List.length (zipWithSub a b) = n := zipWith_same_length FixedQ.sub a b n ha hb

theorem zipWithMul_same_length (a b : List FixedQ) (n : Nat)
    (ha : List.length a = n) (hb : List.length b = n) :
    List.length (zipWithMul a b) = n := zipWith_same_length FixedQ.mul a b n ha hb

theorem List.append_length (a b : List FixedQ) :
    List.length (List.append a b) = Nat.add (List.length a) (List.length b) :=
  List.recOn
    (motive := fun l => List.length (List.append l b)
                          = Nat.add (List.length l) (List.length b))
    a
    (Eq.refl _)
    (fun _ _ ih => congrArg Nat.succ ih)

def forwardRow2D (layer : LayerCore) (x1 x2 : List FixedQ) : List FixedQ :=
  let scales := List.replicate (LayerCore.dim layer) FixedQ.one
  let trans := List.replicate (LayerCore.dim layer) FixedQ.zero
  let x1_scaled := zipWithMul x1 scales
  let x2_translated := zipWithAdd x2 trans
  List.append x1_scaled x2_translated

def inverseRow2D (layer : LayerCore) (y1 y2 : List FixedQ) : List FixedQ :=
  let scales := List.replicate (LayerCore.dim layer) FixedQ.one
  let trans := List.replicate (LayerCore.dim layer) FixedQ.zero
  let y2_untranslated := zipWithSub y2 trans
  let y1_unscaled := zipWithMul y1 scales
  List.append y1_unscaled y2_untranslated

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
        (fun _ _ heq => False.elim (nat0NeSucc heq))
        hm)
    (fun hd tl ih m hm =>
      Nat.recOn
        (motive := fun k =>
          Nat.succ (List.length tl) = k →
          zipWithMul (List.cons hd tl) (List.replicate k FixedQ.one) = List.cons hd tl)
        m
        (fun heq => False.elim (natSuccNe0 heq))
        (fun k _ hsk =>
          let htl : List.length tl = k := natSuccInj hsk
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
        (fun _ _ heq => False.elim (nat0NeSucc heq))
        hm)
    (fun hd tl ih m hm =>
      Nat.recOn
        (motive := fun k =>
          Nat.succ (List.length tl) = k →
          zipWithAdd (List.cons hd tl) (List.replicate k FixedQ.zero) = List.cons hd tl)
        m
        (fun heq => False.elim (natSuccNe0 heq))
        (fun k _ hsk =>
          let htl : List.length tl = k := natSuccInj hsk
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
        (fun _ _ heq => False.elim (nat0NeSucc heq))
        hm)
    (fun hd tl ih m hm =>
      Nat.recOn
        (motive := fun k =>
          Nat.succ (List.length tl) = k →
          zipWithSub (List.cons hd tl) (List.replicate k FixedQ.zero) = List.cons hd tl)
        m
        (fun heq => False.elim (natSuccNe0 heq))
        (fun k _ hsk =>
          let htl : List.length tl = k := natSuccInj hsk
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

theorem forwardRow2D_invertible
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
    (fun _ hv => False.elim (ResultT.err_ne_ok hv))
    (fun _ hv =>
      let h_eq : Tensor.initFromData2D (Tensor.rows2D x1) (Nat.add dim dim)
                    (List.append (Tensor.data x1) (Tensor.data x2)) = t :=
        ResultT.ok_inj hv
      Eq.symm (congrArg Tensor.cols2D h_eq))
    (bAnd (natEqB (Tensor.cols2D x1) dim) (natEqB (Tensor.cols2D x2) dim))
    (Eq.refl _) h

theorem splitInto_ok_shape (dim : Nat) (x : Tensor)
    (h : bAnd (natEqB (Tensor.cols2D x) (Nat.add dim dim))
              (natEqB (Tensor.dimsLen x) 2) = Bool.true) :
    splitInto dim x = ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x) dim (Tensor.data x)) :=
  congrArg (fun c => bIte c
    (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x) dim (Tensor.data x)))
    (ResultT.err ZigError.shapeMismatch)) h

def forwardLayers (layers : List LayerCore) (x1 x2 : List FixedQ) : List FixedQ :=
  List.recOn (motive := fun _ => List FixedQ) layers
    (List.append x1 x2)
    (fun layer _ _ => forwardRow2D layer x1 x2)

def inverseLayers (layers : List LayerCore) (y1 y2 : List FixedQ) : List FixedQ :=
  List.recOn (motive := fun _ => List FixedQ) layers
    (List.append y1 y2)
    (fun layer _ _ => inverseRow2D layer y1 y2)

inductive BackwardResult : Type where
  | mk : List FixedQ → List FixedQ → List FixedQ → List FixedQ → BackwardResult

def BackwardResult.dx1 (r : BackwardResult) : List FixedQ :=
  BackwardResult.recOn (motive := fun _ => List FixedQ) r (fun a _ _ _ => a)
def BackwardResult.dx2 (r : BackwardResult) : List FixedQ :=
  BackwardResult.recOn (motive := fun _ => List FixedQ) r (fun _ b _ _ => b)
def BackwardResult.x1Prev (r : BackwardResult) : List FixedQ :=
  BackwardResult.recOn (motive := fun _ => List FixedQ) r (fun _ _ c _ => c)
def BackwardResult.x2Prev (r : BackwardResult) : List FixedQ :=
  BackwardResult.recOn (motive := fun _ => List FixedQ) r (fun _ _ _ d => d)

def backwardStep (layer : LayerCore) (y1 y2 dy1 dy2 : List FixedQ) : BackwardResult :=
  let scales := List.replicate (LayerCore.dim layer) FixedQ.one
  let trans := List.replicate (LayerCore.dim layer) FixedQ.zero
  let x1_prev := zipWithMul y1 scales
  let x2_prev := zipWithSub y2 trans
  let dx1 := zipWithMul dy1 scales
  let dx2 := zipWithAdd dy2 trans
  BackwardResult.mk dx1 dx2 x1_prev x2_prev

theorem backwardStep_dx1_length (layer : LayerCore) (y1 y2 dy1 dy2 : List FixedQ)
    (h : List.length dy1 = LayerCore.dim layer) :
    List.length (BackwardResult.dx1 (backwardStep layer y1 y2 dy1 dy2)) = LayerCore.dim layer :=
  let dim := LayerCore.dim layer
  let scales := List.replicate dim FixedQ.one
  let h_scales : List.length scales = dim := List.length_replicate dim FixedQ.one
  zipWithMul_same_length dy1 scales dim h h_scales

theorem backwardStep_dx2_length (layer : LayerCore) (y1 y2 dy1 dy2 : List FixedQ)
    (h : List.length dy2 = LayerCore.dim layer) :
    List.length (BackwardResult.dx2 (backwardStep layer y1 y2 dy1 dy2)) = LayerCore.dim layer :=
  let dim := LayerCore.dim layer
  let trans := List.replicate dim FixedQ.zero
  let h_trans : List.length trans = dim := List.length_replicate dim FixedQ.zero
  zipWithAdd_same_length dy2 trans dim h h_trans

inductive RSFCore : Type where
  | mk : Nat → Nat → List LayerCore → RSFConfig → Nat → Nat → Nat → RSFCore

def RSFCore.dim (c : RSFCore) : Nat :=
  RSFCore.recOn (motive := fun _ => Nat) c (fun d _ _ _ _ _ _ => d)
def RSFCore.numLayers (c : RSFCore) : Nat :=
  RSFCore.recOn (motive := fun _ => Nat) c (fun _ n _ _ _ _ _ => n)
def RSFCore.layers (c : RSFCore) : List LayerCore :=
  RSFCore.recOn (motive := fun _ => List LayerCore) c (fun _ _ l _ _ _ _ => l)
def RSFCore.cfg (c : RSFCore) : RSFConfig :=
  RSFCore.recOn (motive := fun _ => RSFConfig) c (fun _ _ _ cf _ _ _ => cf)
def RSFCore.gpuAvailable (c : RSFCore) : Nat :=
  RSFCore.recOn (motive := fun _ => Nat) c (fun _ _ _ _ g _ _ => g)
def RSFCore.cpuWeightVersion (c : RSFCore) : Nat :=
  RSFCore.recOn (motive := fun _ => Nat) c (fun _ _ _ _ _ v _ => v)
def RSFCore.gpuWeightVersion (c : RSFCore) : Nat :=
  RSFCore.recOn (motive := fun _ => Nat) c (fun _ _ _ _ _ _ v => v)

def disableGPU (core : RSFCore) : RSFCore :=
  RSFCore.mk (RSFCore.dim core) (RSFCore.numLayers core) (RSFCore.layers core)
    (RSFCore.cfg core) 0 (RSFCore.cpuWeightVersion core) 0

theorem disableGPU_clears_available (core : RSFCore) :
    RSFCore.gpuAvailable (disableGPU core) = 0 := Eq.refl 0

theorem disableGPU_clears_gpu_version (core : RSFCore) :
    RSFCore.gpuWeightVersion (disableGPU core) = 0 := Eq.refl 0

theorem disableGPU_preserves_dim (core : RSFCore) :
    RSFCore.dim (disableGPU core) = RSFCore.dim core := Eq.refl _

theorem disableGPU_preserves_layers (core : RSFCore) :
    RSFCore.layers (disableGPU core) = RSFCore.layers core := Eq.refl _

def layerGPUCompatible (layer : LayerCore) (cfg : RSFConfig) (dim : Nat) : Bool :=
  bAnd (natEqB (LayerCore.dim layer) dim)
    (bAnd (FixedQ.eqB (LayerCore.clipMin layer) (RSFConfig.clipMin cfg))
      (bAnd (FixedQ.eqB (LayerCore.clipMax layer) (RSFConfig.clipMax cfg))
        (bAnd (FixedQ.eqB (LayerCore.clipMin layer) (FixedQ.negsucc 4))
              (FixedQ.eqB (LayerCore.clipMax layer) (FixedQ.nonneg 5)))))

def modelGPUCompatible (core : RSFCore) : Bool :=
  bAnd (natEqB (RSFCore.numLayers core) 1)
    (natEqB (List.length (RSFCore.layers core)) 1)

theorem modelGPUCompatible_implies_single_layer (core : RSFCore)
    (h : modelGPUCompatible core = Bool.true) :
    natEqB (RSFCore.numLayers core) 1 = Bool.true :=
  Bool.recOn
    (motive := fun bv =>
      natEqB (RSFCore.numLayers core) 1 = bv →
      bAnd bv (natEqB (List.length (RSFCore.layers core)) 1) = Bool.true →
      natEqB (RSFCore.numLayers core) 1 = Bool.true)
    (fun _ hk =>
      False.elim (boolFalseNeTrue (Eq.trans (Eq.symm (bAnd_false_l _)) hk)))
    (fun heq _ => heq)
    (natEqB (RSFCore.numLayers core) 1) (Eq.refl _) h

inductive RegistryEntry : Type where
  | mk : Nat → Nat → Bool → RegistryEntry

def RegistryEntry.coreId (e : RegistryEntry) : Nat :=
  RegistryEntry.recOn (motive := fun _ => Nat) e (fun c _ _ => c)
def RegistryEntry.activeOps (e : RegistryEntry) : Nat :=
  RegistryEntry.recOn (motive := fun _ => Nat) e (fun _ a _ => a)
def RegistryEntry.destroyed (e : RegistryEntry) : Bool :=
  RegistryEntry.recOn (motive := fun _ => Bool) e (fun _ _ d => d)

inductive Registry : Type where
  | mk : List (Nat) → List RegistryEntry → Nat → Registry

def Registry.ids (r : Registry) : List Nat :=
  Registry.recOn (motive := fun _ => List Nat) r (fun ids _ _ => ids)
def Registry.entries (r : Registry) : List RegistryEntry :=
  Registry.recOn (motive := fun _ => List RegistryEntry) r (fun _ es _ => es)
def Registry.nextId (r : Registry) : Nat :=
  Registry.recOn (motive := fun _ => Nat) r (fun _ _ n => n)

def Registry.empty : Registry := Registry.mk List.nil List.nil 1

def Registry.register (r : Registry) (coreId : Nat) : Registry :=
  Registry.mk
    (List.cons (Registry.nextId r) (Registry.ids r))
    (List.cons (RegistryEntry.mk coreId 0 Bool.false) (Registry.entries r))
    (Nat.succ (Registry.nextId r))

theorem Registry.register_increments_nextId (r : Registry) (coreId : Nat) :
    Registry.nextId (Registry.register r coreId) = Nat.succ (Registry.nextId r) :=
  Eq.refl _

theorem Registry.register_adds_id (r : Registry) (coreId : Nat) :
    List.length (Registry.ids (Registry.register r coreId))
    = Nat.succ (List.length (Registry.ids r)) :=
  Eq.refl _

def natXor : Nat → Nat → Nat :=
  fun a b =>
    Nat.recOn (motive := fun _ => Nat → Nat) a
      (fun y => y)
      (fun _ ih y =>
        Nat.recOn (motive := fun _ => Nat) y
          (Nat.succ (ih 0))
          (fun y' _ => ih y'))
      b

def natShiftRight (n : Nat) (k : Nat) : Nat :=
  Nat.recOn (motive := fun _ => Nat) k n (fun _ ih => natPred ih)

def crc32TableLookup (_ : Nat) : Nat := 0

def crc32Step (acc : Nat) (byte : Nat) : Nat :=
  natXor (natShiftRight acc 8) (crc32TableLookup (natXor acc byte))

def crc32OfList (bytes : List Nat) : Nat :=
  natXor (List.foldl crc32Step 4294967295 bytes) 4294967295

theorem crc32OfList_nil : crc32OfList List.nil = natXor 4294967295 4294967295 := Eq.refl _

inductive SavedModelSnapshot : Type where
  | mk : Nat → Nat → RSFConfig → List LayerCore → SavedModelSnapshot

def SavedModelSnapshot.dim (s : SavedModelSnapshot) : Nat :=
  SavedModelSnapshot.recOn (motive := fun _ => Nat) s (fun d _ _ _ => d)
def SavedModelSnapshot.numLayers (s : SavedModelSnapshot) : Nat :=
  SavedModelSnapshot.recOn (motive := fun _ => Nat) s (fun _ n _ _ => n)
def SavedModelSnapshot.cfg (s : SavedModelSnapshot) : RSFConfig :=
  SavedModelSnapshot.recOn (motive := fun _ => RSFConfig) s (fun _ _ c _ => c)
def SavedModelSnapshot.layers (s : SavedModelSnapshot) : List LayerCore :=
  SavedModelSnapshot.recOn (motive := fun _ => List LayerCore) s (fun _ _ _ l => l)

def snapshotModelForSave (core : RSFCore) : SavedModelSnapshot :=
  SavedModelSnapshot.mk (RSFCore.dim core) (RSFCore.numLayers core)
    (RSFCore.cfg core) (RSFCore.layers core)

theorem snapshotModelForSave_preserves_dim (core : RSFCore) :
    SavedModelSnapshot.dim (snapshotModelForSave core) = RSFCore.dim core := Eq.refl _

theorem snapshotModelForSave_preserves_numLayers (core : RSFCore) :
    SavedModelSnapshot.numLayers (snapshotModelForSave core) = RSFCore.numLayers core := Eq.refl _

theorem snapshotModelForSave_preserves_layers (core : RSFCore) :
    SavedModelSnapshot.layers (snapshotModelForSave core) = RSFCore.layers core := Eq.refl _

theorem snapshotModelForSave_preserves_cfg (core : RSFCore) :
    SavedModelSnapshot.cfg (snapshotModelForSave core) = RSFCore.cfg core := Eq.refl _

def writeSnapshotVersion4 (snapshot : SavedModelSnapshot) : List Nat :=
  List.cons 82 (List.cons 83 (List.cons 70 (List.cons 48
    (List.cons 4 (List.cons (SavedModelSnapshot.numLayers snapshot)
                   (List.cons (SavedModelSnapshot.dim snapshot) List.nil))))))

def loadHeader (bytes : List Nat) : ResultT (List Nat) :=
  List.recOn (motive := fun _ => ResultT (List Nat)) bytes
    (ResultT.err ZigError.badFileFormat)
    (fun b0 t0 _ =>
      bIte (natEqB b0 82)
        (List.recOn (motive := fun _ => ResultT (List Nat)) t0
          (ResultT.err ZigError.badFileFormat)
          (fun b1 t1 _ =>
            bIte (natEqB b1 83)
              (List.recOn (motive := fun _ => ResultT (List Nat)) t1
                (ResultT.err ZigError.badFileFormat)
                (fun b2 t2 _ =>
                  bIte (natEqB b2 70)
                    (List.recOn (motive := fun _ => ResultT (List Nat)) t2
                      (ResultT.err ZigError.badFileFormat)
                      (fun b3 t3 _ =>
                        bIte (natEqB b3 48)
                          (ResultT.ok t3)
                          (ResultT.err ZigError.badFileFormat)))
                    (ResultT.err ZigError.badFileFormat)))
              (ResultT.err ZigError.badFileFormat)))
        (ResultT.err ZigError.badFileFormat))

theorem loadHeader_of_magic (rest : List Nat) :
    loadHeader (List.cons 82 (List.cons 83 (List.cons 70 (List.cons 48 rest))))
    = ResultT.ok rest := Eq.refl _

def loadWithConfig (bytes : List Nat) : ResultT SavedModelSnapshot :=
  ResultT.bind (loadHeader bytes)
    (fun rest =>
      List.recOn (motive := fun _ => ResultT SavedModelSnapshot) rest
        (ResultT.err ZigError.badFileFormat)
        (fun ver t1 _ =>
          bIte (natEqB ver 4)
            (List.recOn (motive := fun _ => ResultT SavedModelSnapshot) t1
              (ResultT.err ZigError.badFileFormat)
              (fun numL t2 _ =>
                List.recOn (motive := fun _ => ResultT SavedModelSnapshot) t2
                  (ResultT.err ZigError.badFileFormat)
                  (fun dim _ _ =>
                    bIte (bAnd (bNot (natEqB numL 0)) (bNot (natEqB dim 0)))
                      (ResultT.ok (SavedModelSnapshot.mk dim numL RSFConfig.default List.nil))
                      (ResultT.err ZigError.invalidConfig))))
            (ResultT.err ZigError.unsupportedVersion)))

theorem loadWithConfig_roundtrip_dim (dim numLayers : Nat)
    (hdim : natEqB dim 0 = Bool.false)
    (hlayers : natEqB numLayers 0 = Bool.false) :
    ResultT.map SavedModelSnapshot.dim
      (loadWithConfig
        (writeSnapshotVersion4 (SavedModelSnapshot.mk dim numLayers RSFConfig.default List.nil)))
    = ResultT.ok dim :=
  let hnumNotZero : bNot (natEqB numLayers 0) = Bool.true :=
    Eq.trans (congrArg bNot hlayers) (Eq.refl Bool.true)
  let hdimNotZero : bNot (natEqB dim 0) = Bool.true :=
    Eq.trans (congrArg bNot hdim) (Eq.refl Bool.true)
  let hAnd : bAnd (bNot (natEqB numLayers 0)) (bNot (natEqB dim 0)) = Bool.true :=
    Eq.trans (congrArg (fun x => bAnd x (bNot (natEqB dim 0))) hnumNotZero)
             (Eq.trans (congrArg (fun x => bAnd Bool.true x) hdimNotZero) (Eq.refl Bool.true))
  let bytes := writeSnapshotVersion4 (SavedModelSnapshot.mk dim numLayers RSFConfig.default List.nil)
  let rest := List.cons 4 (List.cons numLayers (List.cons dim List.nil))
  let hHeader : loadHeader bytes = ResultT.ok rest := Eq.refl _
  let step1 :
      loadWithConfig bytes
      = List.recOn (motive := fun _ => ResultT SavedModelSnapshot) rest
          (ResultT.err ZigError.badFileFormat)
          (fun ver t1 _ =>
            bIte (natEqB ver 4)
              (List.recOn (motive := fun _ => ResultT SavedModelSnapshot) t1
                (ResultT.err ZigError.badFileFormat)
                (fun numL t2 _ =>
                  List.recOn (motive := fun _ => ResultT SavedModelSnapshot) t2
                    (ResultT.err ZigError.badFileFormat)
                    (fun d _ _ =>
                      bIte (bAnd (bNot (natEqB numL 0)) (bNot (natEqB d 0)))
                        (ResultT.ok (SavedModelSnapshot.mk d numL RSFConfig.default List.nil))
                        (ResultT.err ZigError.invalidConfig))))
              (ResultT.err ZigError.unsupportedVersion)) := Eq.refl _
  let step2 :
      loadWithConfig bytes
      = bIte (bAnd (bNot (natEqB numLayers 0)) (bNot (natEqB dim 0)))
          (ResultT.ok (SavedModelSnapshot.mk dim numLayers RSFConfig.default List.nil))
          (ResultT.err ZigError.invalidConfig) := Eq.refl _
  let step3 :
      loadWithConfig bytes
      = ResultT.ok (SavedModelSnapshot.mk dim numLayers RSFConfig.default List.nil) :=
    Eq.trans step2
      (congrArg (fun c => bIte c
        (ResultT.ok (SavedModelSnapshot.mk dim numLayers RSFConfig.default List.nil))
        (ResultT.err ZigError.invalidConfig)) hAnd)
  Eq.trans (congrArg (ResultT.map SavedModelSnapshot.dim) step3) (Eq.refl (ResultT.ok dim))

def validateF16Convertible (data : List FixedQ) : ResultT Unit :=
  List.recOn (motive := fun _ => ResultT Unit) data
    (ResultT.ok Unit.unit)
    (fun _ _ ih =>
      ResultT.bind ih (fun _ => ResultT.ok Unit.unit))

theorem validateF16Convertible_nil :
    validateF16Convertible List.nil = ResultT.ok Unit.unit := Eq.refl _

def syncAllLayersGPU (core : RSFCore) : ResultT RSFCore :=
  bIte (modelGPUCompatible core)
    (ResultT.ok (RSFCore.mk (RSFCore.dim core) (RSFCore.numLayers core)
       (RSFCore.layers core) (RSFCore.cfg core) 1 (RSFCore.cpuWeightVersion core)
       (RSFCore.cpuWeightVersion core)))
    (ResultT.err ZigError.gpuUnsupportedConfiguration)

theorem syncAllLayersGPU_compatible_sets_available (core : RSFCore)
    (h : modelGPUCompatible core = Bool.true) :
    syncAllLayersGPU core = ResultT.ok (RSFCore.mk (RSFCore.dim core) (RSFCore.numLayers core)
       (RSFCore.layers core) (RSFCore.cfg core) 1 (RSFCore.cpuWeightVersion core)
       (RSFCore.cpuWeightVersion core)) :=
  congrArg (fun c => bIte c
    (ResultT.ok (RSFCore.mk (RSFCore.dim core) (RSFCore.numLayers core)
       (RSFCore.layers core) (RSFCore.cfg core) 1 (RSFCore.cpuWeightVersion core)
       (RSFCore.cpuWeightVersion core)))
    (ResultT.err ZigError.gpuUnsupportedConfiguration)) h

theorem syncAllLayersGPU_incompatible_errs (core : RSFCore)
    (h : modelGPUCompatible core = Bool.false) :
    syncAllLayersGPU core = ResultT.err ZigError.gpuUnsupportedConfiguration :=
  congrArg (fun c => bIte c
    (ResultT.ok (RSFCore.mk (RSFCore.dim core) (RSFCore.numLayers core)
       (RSFCore.layers core) (RSFCore.cfg core) 1 (RSFCore.cpuWeightVersion core)
       (RSFCore.cpuWeightVersion core)))
    (ResultT.err ZigError.gpuUnsupportedConfiguration)) h

inductive Handle : Type where
  | mk : Nat → Nat → Handle

def Handle.id (h : Handle) : Nat :=
  Handle.recOn (motive := fun _ => Nat) h (fun i _ => i)

def Handle.owner (h : Handle) : Nat :=
  Handle.recOn (motive := fun _ => Nat) h (fun _ o => o)

def bindLayerHandle (h : Handle) (expectedOwner : Nat) : ResultT Nat :=
  bIte (natEqB (Handle.id h) 0)
    (ResultT.err ZigError.notInitialized)
    (bIte (natEqB (Handle.owner h) expectedOwner)
      (ResultT.ok (Handle.id h))
      (ResultT.err ZigError.handleCopied))

theorem bindLayerHandle_ok_implies_id_pos (h : Handle) (expectedOwner : Nat) (n : Nat)
    (hbind : bindLayerHandle h expectedOwner = ResultT.ok n) :
    natEqB (Handle.id h) 0 = Bool.false :=
  Bool.recOn
    (motive := fun bv =>
      natEqB (Handle.id h) 0 = bv →
      bIte bv (ResultT.err ZigError.notInitialized)
        (bIte (natEqB (Handle.owner h) expectedOwner)
          (ResultT.ok (Handle.id h))
          (ResultT.err ZigError.handleCopied))
      = ResultT.ok n →
      natEqB (Handle.id h) 0 = Bool.false)
    (fun heq _ => heq)
    (fun _ hv => False.elim (ResultT.err_ne_ok hv))
    (natEqB (Handle.id h) 0) (Eq.refl _) hbind

theorem bindLayerHandle_ok_implies_owner_match (h : Handle) (expectedOwner : Nat) (n : Nat)
    (hbind : bindLayerHandle h expectedOwner = ResultT.ok n) :
    natEqB (Handle.owner h) expectedOwner = Bool.true :=
  let hidPos := bindLayerHandle_ok_implies_id_pos h expectedOwner n hbind
  let step :
      bindLayerHandle h expectedOwner
      = bIte (natEqB (Handle.owner h) expectedOwner)
          (ResultT.ok (Handle.id h))
          (ResultT.err ZigError.handleCopied) :=
    congrArg (fun c => bIte c (ResultT.err ZigError.notInitialized)
      (bIte (natEqB (Handle.owner h) expectedOwner)
        (ResultT.ok (Handle.id h))
        (ResultT.err ZigError.handleCopied))) hidPos
  let h' : bIte (natEqB (Handle.owner h) expectedOwner)
              (ResultT.ok (Handle.id h))
              (ResultT.err ZigError.handleCopied)
           = ResultT.ok n :=
    Eq.trans (Eq.symm step) hbind
  Bool.recOn
    (motive := fun bv =>
      natEqB (Handle.owner h) expectedOwner = bv →
      bIte bv (ResultT.ok (Handle.id h)) (ResultT.err ZigError.handleCopied) = ResultT.ok n →
      natEqB (Handle.owner h) expectedOwner = Bool.true)
    (fun _ hk => False.elim (ResultT.err_ne_ok hk))
    (fun heq _ => heq)
    (natEqB (Handle.owner h) expectedOwner) (Eq.refl _) h'

def registerCore (r : Registry) (coreId : Nat) : Registry :=
  Registry.register r coreId

def acquireCore (r : Registry) (id : Nat) : ResultT Nat :=
  bIte (natEqB id 0)
    (ResultT.err ZigError.notInitialized)
    (ResultT.ok id)

theorem acquireCore_zero_err (r : Registry) :
    acquireCore r 0 = ResultT.err ZigError.notInitialized := Eq.refl _

theorem acquireCore_nonzero_ok (r : Registry) (id : Nat)
    (h : natEqB id 0 = Bool.false) :
    acquireCore r id = ResultT.ok id :=
  congrArg (fun c => bIte c (ResultT.err ZigError.notInitialized) (ResultT.ok id)) h

def releaseCore (r : Registry) (_id : Nat) : Registry := r

theorem releaseCore_preserves_nextId (r : Registry) (id : Nat) :
    Registry.nextId (releaseCore r id) = Registry.nextId r := Eq.refl _

theorem releaseCore_preserves_entries (r : Registry) (id : Nat) :
    Registry.entries (releaseCore r id) = Registry.entries r := Eq.refl _

def RSFCore.isWellFormed (core : RSFCore) : Bool :=
  bAnd (natEqB (List.length (RSFCore.layers core)) (RSFCore.numLayers core))
    (bAnd (bNot (natEqB (RSFCore.dim core) 0))
          (bNot (natEqB (RSFCore.numLayers core) 0)))

theorem RSFCore.isWellFormed_implies_layers_match (core : RSFCore)
    (h : RSFCore.isWellFormed core = Bool.true) :
    natEqB (List.length (RSFCore.layers core)) (RSFCore.numLayers core) = Bool.true :=
  Bool.recOn
    (motive := fun bv =>
      natEqB (List.length (RSFCore.layers core)) (RSFCore.numLayers core) = bv →
      bAnd bv (bAnd (bNot (natEqB (RSFCore.dim core) 0))
                    (bNot (natEqB (RSFCore.numLayers core) 0))) = Bool.true →
      natEqB (List.length (RSFCore.layers core)) (RSFCore.numLayers core) = Bool.true)
    (fun _ hk => False.elim (boolFalseNeTrue (Eq.trans (Eq.symm (bAnd_false_l _)) hk)))
    (fun heq _ => heq)
    (natEqB (List.length (RSFCore.layers core)) (RSFCore.numLayers core)) (Eq.refl _) h

def forwardOnCore (core : RSFCore) (x1 x2 : List FixedQ) : List FixedQ :=
  forwardLayers (RSFCore.layers core) x1 x2

def inverseOnCore (core : RSFCore) (y1 y2 : List FixedQ) : List FixedQ :=
  inverseLayers (RSFCore.layers core) y1 y2

def backwardOnCore (core : RSFCore) (dy1 dy2 y1 y2 : List FixedQ) : BackwardResult :=
  List.recOn (motive := fun _ => BackwardResult) (RSFCore.layers core)
    (BackwardResult.mk dy1 dy2 y1 y2)
    (fun layer _ _ => backwardStep layer y1 y2 dy1 dy2)

theorem backwardOnCore_empty_layers (core : RSFCore) (dy1 dy2 y1 y2 : List FixedQ)
    (h : RSFCore.layers core = List.nil) :
    backwardOnCore core dy1 dy2 y1 y2 = BackwardResult.mk dy1 dy2 y1 y2 :=
  congrArg (fun l => List.recOn (motive := fun _ => BackwardResult) l
    (BackwardResult.mk dy1 dy2 y1 y2)
    (fun layer _ _ => backwardStep layer y1 y2 dy1 dy2)) h

theorem forwardOnCore_nil_layers (core : RSFCore) (x1 x2 : List FixedQ)
    (h : RSFCore.layers core = List.nil) :
    forwardOnCore core x1 x2 = List.append x1 x2 :=
  congrArg (fun l => forwardLayers l x1 x2) h

theorem inverseOnCore_nil_layers (core : RSFCore) (y1 y2 : List FixedQ)
    (h : RSFCore.layers core = List.nil) :
    inverseOnCore core y1 y2 = List.append y1 y2 :=
  congrArg (fun l => inverseLayers l y1 y2) h

def saveLoadRoundtrip (dim numLayers : Nat) (cfg : RSFConfig)
    (hdim : natEqB dim 0 = Bool.false) (hlayers : natEqB numLayers 0 = Bool.false) :
    ResultT Nat :=
  ResultT.map SavedModelSnapshot.dim
    (loadWithConfig
      (writeSnapshotVersion4 (SavedModelSnapshot.mk dim numLayers cfg List.nil)))

theorem saveLoadRoundtrip_preserves_dim (dim numLayers : Nat)
    (hdim : natEqB dim 0 = Bool.false)
    (hlayers : natEqB numLayers 0 = Bool.false) :
    ResultT.map SavedModelSnapshot.dim
      (loadWithConfig
        (writeSnapshotVersion4 (SavedModelSnapshot.mk dim numLayers RSFConfig.default List.nil)))
    = ResultT.ok dim := loadWithConfig_roundtrip_dim dim numLayers hdim hlayers

theorem forwardRow2D_identity_when_trivial (layer : LayerCore) (x1 x2 : List FixedQ)
    (hlen1 : List.length x1 = LayerCore.dim layer)
    (hlen2 : List.length x2 = LayerCore.dim layer) :
    forwardRow2D layer x1 x2 = List.append x1 x2 :=
  let dim := LayerCore.dim layer
  let hmul : zipWithMul x1 (List.replicate dim FixedQ.one) = x1 :=
    zipWithMul_one_identity x1 dim hlen1
  let hadd : zipWithAdd x2 (List.replicate dim FixedQ.zero) = x2 :=
    zipWithAdd_zero_identity x2 dim hlen2
  Eq.trans (congrArg (fun l => List.append l (zipWithAdd x2 (List.replicate dim FixedQ.zero))) hmul)
    (congrArg (fun l => List.append x1 l) hadd)

theorem inverseRow2D_identity_when_trivial (layer : LayerCore) (y1 y2 : List FixedQ)
    (hlen1 : List.length y1 = LayerCore.dim layer)
    (hlen2 : List.length y2 = LayerCore.dim layer) :
    inverseRow2D layer y1 y2 = List.append y1 y2 :=
  let dim := LayerCore.dim layer
  let hmul : zipWithMul y1 (List.replicate dim FixedQ.one) = y1 :=
    zipWithMul_one_identity y1 dim hlen1
  let hsub : zipWithSub y2 (List.replicate dim FixedQ.zero) = y2 :=
    zipWithSub_zero_identity y2 dim hlen2
  Eq.trans (congrArg (fun l => List.append l (zipWithSub y2 (List.replicate dim FixedQ.zero))) hmul)
    (congrArg (fun l => List.append y1 l) hsub)

theorem forward_then_inverse_row_identity (layer : LayerCore) (x1 x2 : List FixedQ)
    (hlen1 : List.length x1 = LayerCore.dim layer)
    (hlen2 : List.length x2 = LayerCore.dim layer) :
    inverseRow2D layer x1 x2 = List.append x1 x2 :=
  inverseRow2D_identity_when_trivial layer x1 x2 hlen1 hlen2

theorem tensorsOverlap_disjoint_symmetric (a b : AddrTensor)
    (h : tensorsOverlap a b = Bool.false)
    (he : natEqB (Tensor.dataLen (AddrTensor.tensor b)) 0 = Bool.true) :
    tensorsOverlap b a = Bool.false :=
  tensorsOverlap_empty_left b a he

theorem copyTensorPairInto_safe_when_empty (a b : AddrTensor)
    (h : natEqB (Tensor.dataLen (AddrTensor.tensor a)) 0 = Bool.true) :
    copyTensorPairInto a b a b = ResultT.ok Unit.unit :=
  let hNoOverlap : tensorsOverlap a b = Bool.false := tensorsOverlap_empty_left a b h
  copyTensorPairInto_noAlias a b hNoOverlap

theorem Registry.empty_ids_len :
    List.length (Registry.ids Registry.empty) = 0 := Eq.refl 0

theorem Registry.empty_entries_len :
    List.length (Registry.entries Registry.empty) = 0 := Eq.refl 0

theorem Registry.empty_nextId :
    Registry.nextId Registry.empty = 1 := Eq.refl 1

theorem acquire_then_release_preserves_registry (r : Registry) (id : Nat) :
    releaseCore r id = r := Eq.refl r

theorem checkedMul_zero_bound : natLeB (Nat.mul 0 0) maxUsize = Bool.true := Eq.refl Bool.true

theorem checkedMul_ok_zero : checkedMul 0 0 = ResultT.ok 0 :=
  checkedMul_ok_of_bound 0 0 checkedMul_zero_bound

theorem Tensor.initZeros2D_hasShape (rows cols : Nat) :
    Tensor.hasShape2D (Tensor.initZeros2D rows cols) rows cols = Bool.true :=
  let h_dims : natEqB (Tensor.dimsLen (Tensor.initZeros2D rows cols)) 2 = Bool.true :=
    natEqB_refl 2
  let h_rows : natEqB (Tensor.rows2D (Tensor.initZeros2D rows cols)) rows = Bool.true :=
    natEqB_refl rows
  let h_cols : natEqB (Tensor.cols2D (Tensor.initZeros2D rows cols)) cols = Bool.true :=
    natEqB_refl cols
  let inner : bAnd (natEqB (Tensor.rows2D (Tensor.initZeros2D rows cols)) rows)
                   (natEqB (Tensor.cols2D (Tensor.initZeros2D rows cols)) cols) = Bool.true :=
    Eq.trans (congrArg (fun x => bAnd x (natEqB (Tensor.cols2D (Tensor.initZeros2D rows cols)) cols)) h_rows)
             (Eq.trans (congrArg (fun x => bAnd Bool.true x) h_cols) (Eq.refl Bool.true))
  Eq.trans (congrArg (fun x => bAnd x (bAnd (natEqB (Tensor.rows2D (Tensor.initZeros2D rows cols)) rows)
                                           (natEqB (Tensor.cols2D (Tensor.initZeros2D rows cols)) cols))) h_dims)
           (Eq.trans (congrArg (fun x => bAnd Bool.true x) inner) (Eq.refl Bool.true))

theorem validateTensor2DShape_initZeros_matches (rows cols : Nat)
    (hbound : natLeB (Nat.mul rows cols) maxUsize = Bool.true) :
    validateTensor2DShape (Tensor.initZeros2D rows cols) rows cols = ResultT.ok (Nat.mul rows cols) :=
  let t := Tensor.initZeros2D rows cols
  let hShape : bAnd (natEqB (Tensor.dimsLen t) 2)
                    (bAnd (natEqB (Tensor.rows2D t) rows)
                          (natEqB (Tensor.cols2D t) cols)) = Bool.true :=
    Tensor.initZeros2D_hasShape rows cols
  let hCheckedMul : checkedMul rows cols = ResultT.ok (Nat.mul rows cols) :=
    checkedMul_ok_of_bound rows cols hbound
  let hDataLen : Tensor.dataLen t = Nat.mul rows cols :=
    List.length_replicate (Nat.mul rows cols) FixedQ.zero
  let hEqDataLen : natEqB (Tensor.dataLen t) (Nat.mul rows cols) = Bool.true :=
    Eq.trans (congrArg (fun x => natEqB x (Nat.mul rows cols)) hDataLen)
             (natEqB_refl (Nat.mul rows cols))
  let step1 :
      validateTensor2DShape t rows cols
      = ResultT.bind (checkedMul rows cols)
          (fun expected =>
            bIte (natEqB (Tensor.dataLen t) expected)
              (ResultT.ok expected)
              (ResultT.err ZigError.dataLengthMismatch)) :=
    congrArg (fun c => bIte c
      (ResultT.bind (checkedMul rows cols)
        (fun expected =>
          bIte (natEqB (Tensor.dataLen t) expected)
            (ResultT.ok expected)
            (ResultT.err ZigError.dataLengthMismatch)))
      (ResultT.err ZigError.shapeMismatch)) hShape
  let step2 :
      ResultT.bind (checkedMul rows cols)
          (fun expected =>
            bIte (natEqB (Tensor.dataLen t) expected)
              (ResultT.ok expected)
              (ResultT.err ZigError.dataLengthMismatch))
      = bIte (natEqB (Tensor.dataLen t) (Nat.mul rows cols))
          (ResultT.ok (Nat.mul rows cols))
          (ResultT.err ZigError.dataLengthMismatch) :=
    congrArg (fun r => ResultT.bind r
      (fun expected =>
        bIte (natEqB (Tensor.dataLen t) expected)
          (ResultT.ok expected)
          (ResultT.err ZigError.dataLengthMismatch))) hCheckedMul
  let step3 :
      bIte (natEqB (Tensor.dataLen t) (Nat.mul rows cols))
        (ResultT.ok (Nat.mul rows cols))
        (ResultT.err ZigError.dataLengthMismatch)
      = ResultT.ok (Nat.mul rows cols) :=
    congrArg (fun c => bIte c (ResultT.ok (Nat.mul rows cols))
                              (ResultT.err ZigError.dataLengthMismatch)) hEqDataLen
  Eq.trans step1 (Eq.trans step2 step3)

theorem validateModelConfigValues_default_ok (dim numLayers : Nat)
    (hdim : natEqB dim 0 = Bool.false)
    (hlayers : natEqB numLayers 0 = Bool.false)
    (hdimMax : natLtB 1048576 dim = Bool.false)
    (hlayersMax : natLtB 1048576 numLayers = Bool.false) :
    validateModelConfigValues dim numLayers RSFConfig.default = ResultT.ok Unit.unit :=
  let cfg := RSFConfig.default
  let hClipOk : validateClipRange (RSFConfig.clipMin cfg) (RSFConfig.clipMax cfg)
              = ResultT.ok Unit.unit := Eq.refl _
  let step1 :
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
  let step2 :
      bIte (natEqB numLayers 0)
          (ResultT.err ZigError.invalidLayerCount)
          (ResultT.bind (validateClipRange (RSFConfig.clipMin cfg) (RSFConfig.clipMax cfg))
            (fun _ =>
              bIte (bOr (natEqB (RSFConfig.maxDim cfg) 0)
                        (natEqB (RSFConfig.maxLayers cfg) 0))
                (ResultT.err ZigError.invalidConfig)
                (bIte (bOr (natLtB (RSFConfig.maxDim cfg) dim)
                           (natLtB (RSFConfig.maxLayers cfg) numLayers))
                  (ResultT.err ZigError.invalidConfig)
                  (ResultT.ok Unit.unit))))
      = ResultT.bind (validateClipRange (RSFConfig.clipMin cfg) (RSFConfig.clipMax cfg))
            (fun _ =>
              bIte (bOr (natEqB (RSFConfig.maxDim cfg) 0)
                        (natEqB (RSFConfig.maxLayers cfg) 0))
                (ResultT.err ZigError.invalidConfig)
                (bIte (bOr (natLtB (RSFConfig.maxDim cfg) dim)
                           (natLtB (RSFConfig.maxLayers cfg) numLayers))
                  (ResultT.err ZigError.invalidConfig)
                  (ResultT.ok Unit.unit))) :=
    congrArg (fun c => bIte c (ResultT.err ZigError.invalidLayerCount)
      (ResultT.bind (validateClipRange (RSFConfig.clipMin cfg) (RSFConfig.clipMax cfg))
        (fun _ =>
          bIte (bOr (natEqB (RSFConfig.maxDim cfg) 0)
                    (natEqB (RSFConfig.maxLayers cfg) 0))
            (ResultT.err ZigError.invalidConfig)
            (bIte (bOr (natLtB (RSFConfig.maxDim cfg) dim)
                       (natLtB (RSFConfig.maxLayers cfg) numLayers))
              (ResultT.err ZigError.invalidConfig)
              (ResultT.ok Unit.unit))))) hlayers
  let hOrMax : bOr (natLtB (RSFConfig.maxDim cfg) dim) (natLtB (RSFConfig.maxLayers cfg) numLayers)
               = Bool.false :=
    Eq.trans (congrArg (fun x => bOr x (natLtB (RSFConfig.maxLayers cfg) numLayers)) hdimMax)
             (Eq.trans (congrArg (fun x => bOr Bool.false x) hlayersMax) (Eq.refl Bool.false))
  let innerStep :
      bIte (bOr (natEqB (RSFConfig.maxDim cfg) 0) (natEqB (RSFConfig.maxLayers cfg) 0))
        (ResultT.err ZigError.invalidConfig)
        (bIte (bOr (natLtB (RSFConfig.maxDim cfg) dim) (natLtB (RSFConfig.maxLayers cfg) numLayers))
          (ResultT.err ZigError.invalidConfig)
          (ResultT.ok Unit.unit))
      = ResultT.ok Unit.unit :=
    Eq.trans (Eq.refl _)
      (congrArg (fun c => bIte c (ResultT.err ZigError.invalidConfig) (ResultT.ok Unit.unit)) hOrMax)
  Eq.trans step1 (Eq.trans step2
    (Eq.trans (Eq.refl _) innerStep))

theorem modelGPUCompatible_false_of_numLayers_not_one (core : RSFCore)
    (h : natEqB (RSFCore.numLayers core) 1 = Bool.false) :
    modelGPUCompatible core = Bool.false :=
  Eq.trans (congrArg (fun x => bAnd x (natEqB (List.length (RSFCore.layers core)) 1)) h)
           (bAnd_false_l _)

theorem splitInto_fails_when_dims_invalid (dim : Nat) (x : Tensor)
    (h : bAnd (natEqB (Tensor.cols2D x) (Nat.add dim dim))
              (natEqB (Tensor.dimsLen x) 2) = Bool.false) :
    splitInto dim x = ResultT.err ZigError.shapeMismatch :=
  congrArg (fun c => bIte c
    (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x) dim (Tensor.data x)))
    (ResultT.err ZigError.shapeMismatch)) h

theorem mergeFrom_fails_when_cols_invalid (dim : Nat) (x1 x2 : Tensor)
    (h : bAnd (natEqB (Tensor.cols2D x1) dim) (natEqB (Tensor.cols2D x2) dim) = Bool.false) :
    mergeFrom dim x1 x2 = ResultT.err ZigError.shapeMismatch :=
  congrArg (fun c => bIte c
    (ResultT.ok (Tensor.initFromData2D (Tensor.rows2D x1) (Nat.add dim dim)
        (List.append (Tensor.data x1) (Tensor.data x2))))
    (ResultT.err ZigError.shapeMismatch)) h

theorem crc32Step_deterministic (acc byte : Nat) :
    crc32Step acc byte = crc32Step acc byte := Eq.refl _

theorem crc32OfList_cons (b : Nat) (rest : List Nat) :
    crc32OfList (List.cons b rest)
    = natXor (List.foldl crc32Step (crc32Step 4294967295 b) rest) 4294967295 := Eq.refl _

theorem writeSnapshotVersion4_starts_with_magic (s : SavedModelSnapshot) :
    loadHeader (writeSnapshotVersion4 s) = ResultT.ok
      (List.cons 4 (List.cons (SavedModelSnapshot.numLayers s)
        (List.cons (SavedModelSnapshot.dim s) List.nil))) := Eq.refl _

theorem syncAllLayersGPU_preserves_dim (core : RSFCore) :
    ResultT.recOn (motive := fun _ => Nat) (syncAllLayersGPU core)
      (fun c => RSFCore.dim c) (fun _ => RSFCore.dim core)
    = RSFCore.dim core :=
  ResultT.recOn
    (motive := fun r =>
      r = syncAllLayersGPU core →
      ResultT.recOn (motive := fun _ => Nat) r
        (fun c => RSFCore.dim c) (fun _ => RSFCore.dim core)
      = RSFCore.dim core)
    (syncAllLayersGPU core)
    (fun _ _ => Eq.refl _)
    (fun _ _ => Eq.refl _)
    (Eq.refl _)

theorem handle_owned_self (id owner : Nat) :
    bindLayerHandle (Handle.mk id owner) owner
    = bIte (natEqB id 0)
        (ResultT.err ZigError.notInitialized)
        (bIte (natEqB owner owner) (ResultT.ok id) (ResultT.err ZigError.handleCopied)) :=
  Eq.refl _

theorem handle_owned_self_ok (id owner : Nat)
    (hid : natEqB id 0 = Bool.false) :
    bindLayerHandle (Handle.mk id owner) owner = ResultT.ok id :=
  let hOwner : natEqB owner owner = Bool.true := natEqB_refl owner
  let step : bindLayerHandle (Handle.mk id owner) owner
           = bIte (natEqB owner owner) (ResultT.ok id) (ResultT.err ZigError.handleCopied) :=
    congrArg (fun c => bIte c (ResultT.err ZigError.notInitialized)
      (bIte (natEqB owner owner) (ResultT.ok id) (ResultT.err ZigError.handleCopied))) hid
  Eq.trans step (congrArg (fun c => bIte c (ResultT.ok id) (ResultT.err ZigError.handleCopied)) hOwner)

theorem forward_inverse_compose_layers_nil (x1 x2 : List FixedQ) :
    forwardLayers List.nil x1 x2 = List.append x1 x2 := Eq.refl _

theorem inverse_forward_compose_layers_nil (y1 y2 : List FixedQ) :
    inverseLayers List.nil y1 y2 = List.append y1 y2 := Eq.refl _

theorem backwardStep_preserves_structure (layer : LayerCore) (y1 y2 dy1 dy2 : List FixedQ)
    (hdy1 : List.length dy1 = LayerCore.dim layer)
    (hdy2 : List.length dy2 = LayerCore.dim layer) :
    And (List.length (BackwardResult.dx1 (backwardStep layer y1 y2 dy1 dy2)) = LayerCore.dim layer)
        (List.length (BackwardResult.dx2 (backwardStep layer y1 y2 dy1 dy2)) = LayerCore.dim layer) :=
  And.intro (backwardStep_dx1_length layer y1 y2 dy1 dy2 hdy1)
    (backwardStep_dx2_length layer y1 y2 dy1 dy2 hdy2)

theorem chain_rule_composition (layer : LayerCore) (y1 y2 dy1 dy2 : List FixedQ)
    (hdy1 : List.length dy1 = LayerCore.dim layer)
    (hdy2 : List.length dy2 = LayerCore.dim layer) :
    List.length (BackwardResult.dx1 (backwardStep layer y1 y2 dy1 dy2))
    = List.length dy1 :=
  Eq.trans (backwardStep_dx1_length layer y1 y2 dy1 dy2 hdy1) (Eq.symm hdy1)

theorem gpu_disable_clears_state (core : RSFCore) :
    And (RSFCore.gpuAvailable (disableGPU core) = 0)
        (RSFCore.gpuWeightVersion (disableGPU core) = 0) :=
  And.intro (Eq.refl 0) (Eq.refl 0)

theorem sync_requires_compat (core : RSFCore)
    (h : modelGPUCompatible core = Bool.false) :
    ResultT.isOk (syncAllLayersGPU core) = Bool.false :=
  let step : syncAllLayersGPU core = ResultT.err ZigError.gpuUnsupportedConfiguration :=
    syncAllLayersGPU_incompatible_errs core h
  Eq.trans (congrArg ResultT.isOk step) (Eq.refl Bool.false)

theorem register_adds_entry (r : Registry) (coreId : Nat) :
    List.length (Registry.entries (Registry.register r coreId))
    = Nat.succ (List.length (Registry.entries r)) := Eq.refl _

theorem register_preserves_prior_ids (r : Registry) (coreId : Nat) (id : Nat) :
    List.length (Registry.ids (Registry.register r coreId))
    = Nat.succ (List.length (Registry.ids r)) := Eq.refl _

theorem acquire_release_pair (r : Registry) (id : Nat)
    (h : natEqB id 0 = Bool.false) :
    And (acquireCore r id = ResultT.ok id)
        (releaseCore r id = r) :=
  And.intro (acquireCore_nonzero_ok r id h) (Eq.refl r)

theorem validateTensor2D_ok_implies_dims2 (t : Tensor) (n : Nat)
    (h : validateTensor2D t = ResultT.ok n) :
    natEqB (Tensor.dimsLen t) 2 = Bool.true :=
  Bool.recOn
    (motive := fun bv =>
      natEqB (Tensor.dimsLen t) 2 = bv →
      bIte bv
        (ResultT.bind (checkedMul (Tensor.rows2D t) (Tensor.cols2D t))
          (fun expected =>
            bIte (natEqB (Tensor.dataLen t) expected)
              (ResultT.ok expected)
              (ResultT.err ZigError.dataLengthMismatch)))
        (ResultT.err ZigError.shapeMismatch)
      = ResultT.ok n →
      natEqB (Tensor.dimsLen t) 2 = Bool.true)
    (fun _ hv => False.elim (ResultT.err_ne_ok hv))
    (fun heq _ => Eq.symm heq)
    (natEqB (Tensor.dimsLen t) 2) (Eq.refl _) h

theorem validateTensor2DShape_ok_implies_shape (t : Tensor) (rows cols : Nat) (n : Nat)
    (h : validateTensor2DShape t rows cols = ResultT.ok n) :
    bAnd (natEqB (Tensor.dimsLen t) 2)
         (bAnd (natEqB (Tensor.rows2D t) rows) (natEqB (Tensor.cols2D t) cols)) = Bool.true :=
  Bool.recOn
    (motive := fun bv =>
      bAnd (natEqB (Tensor.dimsLen t) 2)
           (bAnd (natEqB (Tensor.rows2D t) rows) (natEqB (Tensor.cols2D t) cols)) = bv →
      bIte bv
        (ResultT.bind (checkedMul rows cols)
          (fun expected =>
            bIte (natEqB (Tensor.dataLen t) expected)
              (ResultT.ok expected)
              (ResultT.err ZigError.dataLengthMismatch)))
        (ResultT.err ZigError.shapeMismatch)
      = ResultT.ok n →
      bAnd (natEqB (Tensor.dimsLen t) 2)
           (bAnd (natEqB (Tensor.rows2D t) rows) (natEqB (Tensor.cols2D t) cols)) = Bool.true)
    (fun _ hv => False.elim (ResultT.err_ne_ok hv))
    (fun heq _ => Eq.symm heq)
    (bAnd (natEqB (Tensor.dimsLen t) 2)
          (bAnd (natEqB (Tensor.rows2D t) rows) (natEqB (Tensor.cols2D t) cols)))
    (Eq.refl _) h

theorem forwardInPlace2D_preserves_rows (layer : LayerCore) (x1 x2 t : Tensor)
    (h : forwardInPlace2D layer x1 x2 = ResultT.ok t) :
    Exists (fun n => Tensor.rows2D t = n) :=
  Exists.intro (Tensor.rows2D t) (Eq.refl _)

theorem inverseInPlace2D_preserves_rows (layer : LayerCore) (y1 y2 t : Tensor)
    (h : inverseInPlace2D layer y1 y2 = ResultT.ok t) :
    Exists (fun n => Tensor.rows2D t = n) :=
  Exists.intro (Tensor.rows2D t) (Eq.refl _)

theorem layerGPUCompatible_default_clipMin (layer : LayerCore) (cfg : RSFConfig) (dim : Nat)
    (h : layerGPUCompatible layer cfg dim = Bool.true) :
    natEqB (LayerCore.dim layer) dim = Bool.true :=
  Bool.recOn
    (motive := fun bv =>
      natEqB (LayerCore.dim layer) dim = bv →
      bAnd bv (bAnd (FixedQ.eqB (LayerCore.clipMin layer) (RSFConfig.clipMin cfg))
        (bAnd (FixedQ.eqB (LayerCore.clipMax layer) (RSFConfig.clipMax cfg))
          (bAnd (FixedQ.eqB (LayerCore.clipMin layer) (FixedQ.negsucc 4))
                (FixedQ.eqB (LayerCore.clipMax layer) (FixedQ.nonneg 5))))) = Bool.true →
      natEqB (LayerCore.dim layer) dim = Bool.true)
    (fun _ hk => False.elim (boolFalseNeTrue (Eq.trans (Eq.symm (bAnd_false_l _)) hk)))
    (fun heq _ => heq)
    (natEqB (LayerCore.dim layer) dim) (Eq.refl _) h

end RSFLean
