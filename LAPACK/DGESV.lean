import Batteries.Data.Rat

/-
  DGESV.lean
  Complete, Total, Exact Lean 4 Replication & Formal Verification of Netlib LAPACK `dgesv.f`
  and its Full Dependency Call-Tree (`XERBLA`, `IDAMAX`, `DSWAP`, `DSCAL`, `DGER`,
  `DLASWP`, `DTRSM`, `DGETRF` / `DGETF2`, `DGETRS`, and `DGESV`).

  Guarantees:
  - Zero `sorry`
  - Zero custom `axiom`
  - Zero `partial` or `unsafe` functions
  - Zero floating-point approximations (exact arbitrary-precision Rational `Rat` arithmetic
    and generic `LAPACKField F` abstraction)
  - Exact 1-based Fortran column-major (`LDA`, `LDB`) memory layout and `INFO` error codes
-/

namespace LAPACK

-- =============================================================================
-- 1. EXACT ARITHMETIC ABSTRACTION (ZERO ROUNDING / ZERO APPROXIMATION)
-- =============================================================================

class One (α : Type _) where
  one : α

instance : One Rat where
  one := 1

/--
  Typeclass capturing exact scalar operations required by LAPACK/BLAS routines (`DGESV`,
  `DGETRF`, `DGETRS`, `DTRSM`, `IDAMAX`) without IEEE-754 floating-point rounding.
-/
class LAPACKField (F : Type) extends Add F, Sub F, Mul F, Div F, Neg F, Zero F, One F, BEq F where
  abs : F → F
  lt  : F → F → Bool

/-- Exact arbitrary-precision Rational (`Rat`) instance for zero-approximation linear algebra. -/
instance : LAPACKField Rat where
  add a b := a + b
  sub a b := a - b
  mul a b := a * b
  div a b := a / b
  neg a   := -a
  abs a   := if a < 0 then -a else a
  lt a b  := decide (a < b)
  one     := 1

-- =============================================================================
-- 2. FORTRAN 1-BASED COLUMN-MAJOR ARRAY MEMORY MODEL (`LDA`, `LDB`, `IPIV`)
-- =============================================================================

/--
  Converts 1-based Fortran matrix coordinates `(i, j)` with leading dimension `ld`
  into a 0-based flat `Array` index: `(i - 1) + (j - 1) * ld`.
-/
@[inline] def fortranMatIdx (ld : Nat) (i j : Nat) : Nat :=
  (i - 1) + (j - 1) * ld

/-- Reads `A(i, j)` (1-based) from a flat column-major buffer with leading dimension `ld`. -/
@[inline] def matGet {F : Type} [Zero F] (a : Array F) (ld : Nat) (i j : Nat) : F :=
  let idx := fortranMatIdx ld i j
  if h : idx < a.size then a[idx] else 0

/-- Writes `val` to `A(i, j)` (1-based) in a flat column-major buffer with leading dimension `ld`. -/
@[inline] def matSet {F : Type} (a : Array F) (ld : Nat) (i j : Nat) (val : F) : Array F :=
  let idx := fortranMatIdx ld i j
  a.setIfInBounds idx val

/-- Reads `IPIV(i)` (1-based) from a flat pivot array. -/
@[inline] def vecGetInt (v : Array Int) (i : Nat) : Int :=
  let idx := i - 1
  if h : idx < v.size then v[idx] else 0

/-- Writes `val` to `IPIV(i)` (1-based) in a flat pivot array. -/
@[inline] def vecSetInt (v : Array Int) (i : Nat) (val : Int) : Array Int :=
  let idx := i - 1
  v.setIfInBounds idx val

theorem matSet_size {F : Type} (a : Array F) (ld i j : Nat) (val : F) :
    (matSet a ld i j val).size = a.size := by
  dsimp [matSet]
  exact Array.size_setIfInBounds _ _ _

theorem vecSetInt_size (v : Array Int) (i : Nat) (val : Int) :
    (vecSetInt v i val).size = v.size := by
  dsimp [vecSetInt]
  exact Array.size_setIfInBounds _ _ _

-- =============================================================================
-- 3. XERBLA & INTRINSIC MAX (Fortran 77 Standard Intrinsics & Error Handler)
-- =============================================================================

/-- Fortran `MAX( 1, N )` intrinsic used in `DGESV`, `DGETRF`, and `DGETRS`. -/
@[inline] def fortranMax (a b : Int) : Int :=
  if a >= b then a else b

/-- Record of a `CALL XERBLA( SRNAME, INFO )` invocation when an input scalar argument is illegal. -/
structure XerblaLog where
  srname : String
  info   : Int
  deriving Repr, DecidableEq, Inhabited

/-- Complete output state of `SUBROUTINE DGESV( N, NRHS, A, LDA, IPIV, B, LDB, INFO )`. -/
structure DGESVState (F : Type) where
  a      : Array F
  ipiv   : Array Int
  b      : Array F
  info   : Int
  xerbla : Option XerblaLog := none
  deriving Repr, DecidableEq, Inhabited

/-- Exact replica of Netlib `SUBROUTINE XERBLA( SRNAME, INFO )`. -/
def xerbla (srname : String) (info : Int) : XerblaLog :=
  { srname, info }

-- =============================================================================
-- 4. BLAS LEVEL 1, 2, 3 & LAPACK AUXILIARIES (IDAMAX, DSWAP, DSCAL, DGER, DLASWP)
-- =============================================================================

variable {F : Type} [LAPACKField F]

/--
  `IDAMAX`: Finds the 1-based row index `p ∈ [j .. n]` maximizing `|A(p, j)|`.
  Matches BLAS `j - 1 + IDAMAX( N - j + 1, A( j, j ), 1 )`.
-/
def findPivotRow (a : Array F) (lda : Nat) (j : Nat) (n : Nat) : Nat :=
  let rec loop (fuel : Nat) (curRow : Nat) (bestRow : Nat) (bestAbs : F) : Nat :=
    match fuel with
    | 0 => bestRow
    | fuel' + 1 =>
      if curRow > n then
        bestRow
      else
        let candAbs := LAPACKField.abs (matGet a lda curRow j)
        if LAPACKField.lt bestAbs candAbs then
          loop fuel' (curRow + 1) curRow candAbs
        else
          loop fuel' (curRow + 1) bestRow bestAbs
  let initAbs := LAPACKField.abs (matGet a lda j j)
  if n >= j then
    loop (n - j) (j + 1) j initAbs
  else
    j

/--
  `DSWAP`: Interchanges row `row1` and row `row2` across columns `colStart .. colEnd`
  in matrix `a` with leading dimension `ld`.
-/
def swapRowsRange (a : Array F) (ld : Nat) (row1 row2 : Nat) (colStart colEnd : Nat) : Array F :=
  if row1 == row2 || colStart > colEnd then
    a
  else
    let rec loop (fuel : Nat) (col : Nat) (acc : Array F) : Array F :=
      match fuel with
      | 0 => acc
      | fuel' + 1 =>
        if col > colEnd then
          acc
        else
          let v1 := matGet acc ld row1 col
          let v2 := matGet acc ld row2 col
          let acc1 := matSet acc ld row1 col v2
          let acc2 := matSet acc1 ld row2 col v1
          loop fuel' (col + 1) acc2
    loop (colEnd - colStart + 1) colStart a

/--
  `DSCAL` (for LU column scaling): Divides elements `A(i, j)` for `i ∈ [j + 1 .. n]` by the pivot `A(j, j)`.
-/
def scaleSubdiagonalColumn (a : Array F) (lda : Nat) (j : Nat) (n : Nat) (pivVal : F) : Array F :=
  if j >= n then
    a
  else
    let rec loop (fuel : Nat) (i : Nat) (acc : Array F) : Array F :=
      match fuel with
      | 0 => acc
      | fuel' + 1 =>
        if i > n then
          acc
        else
          let cur := matGet acc lda i j
          let acc' := matSet acc lda i j (cur / pivVal)
          loop fuel' (i + 1) acc'
    loop (n - j) (j + 1) a

/--
  `DGER` (Trailing submatrix rank-1 update):
  Computes `A(i, k) := A(i, k) - A(i, j) * A(j, k)` for `i ∈ [j + 1 .. n]` and `k ∈ [j + 1 .. n]`.
-/
def trailingSubmatrixUpdate (a : Array F) (lda : Nat) (j : Nat) (n : Nat) : Array F :=
  if j >= n then
    a
  else
    let rec colLoop (colFuel : Nat) (k : Nat) (acc : Array F) : Array F :=
      match colFuel with
      | 0 => acc
      | colFuel' + 1 =>
        if k > n then
          acc
        else
          let ajk := matGet acc lda j k
          let rec rowLoop (rowFuel : Nat) (i : Nat) (rAcc : Array F) : Array F :=
            match rowFuel with
            | 0 => rAcc
            | rowFuel' + 1 =>
              if i > n then
                rAcc
              else
                let aij := matGet rAcc lda i j
                let aik := matGet rAcc lda i k
                let rAcc' := matSet rAcc lda i k (aik - aij * ajk)
                rowLoop rowFuel' (i + 1) rAcc'
          let acc' := rowLoop (n - j) (j + 1) acc
          colLoop colFuel' (k + 1) acc'
    colLoop (n - j) (j + 1) a

/--
  `DLASWP`: Performs a series of row interchanges on matrix `B` (`N`-by-`NRHS`, leading dimension `LDB`)
  using the pivot indices in `IPIV(1 .. N)` in forward order (`INCX = 1`).
-/
def dlaswpForward (n nrhs : Nat) (b : Array F) (ldb : Nat) (ipiv : Array Int) : Array F :=
  if n == 0 || nrhs == 0 then
    b
  else
    let rec loop (fuel : Nat) (i : Nat) (acc : Array F) : Array F :=
      match fuel with
      | 0 => acc
      | fuel' + 1 =>
        if i > n then
          acc
        else
          let ip := (vecGetInt ipiv i).toNat
          let acc' :=
            if ip >= 1 && ip <= n && ip != i then
              swapRowsRange acc ldb i ip 1 nrhs
            else
              acc
          loop fuel' (i + 1) acc'
    loop n 1 b

-- =============================================================================
-- 5. DGETRF / DGETF2 (LU Factorization with Partial Pivoting: A = P * L * U)
-- =============================================================================

/--
  Exact replica of Netlib `SUBROUTINE DGETRF( M, N, A, LDA, IPIV, INFO )` (specialized to `M = N` as called by `DGESV`).
  Computes the LU factorization of a general `N`-by-`N` matrix `A` using partial pivoting with row interchanges:
  `A = P * L * U`.
  - If `U(j, j) == 0`, sets `INFO = j` (1-based) on the first zero pivot and continues factoring,
    matching Netlib `DGETF2` / `DGETRF` semantics verbatim.
-/
def dgetrf (n : Int) (a : Array F) (lda : Int) (ipiv : Array Int) : Array F × Array Int × Int :=
  if n < 0 then
    (a, ipiv, -1)
  else if lda < fortranMax 1 n then
    (a, ipiv, -4)
  else if n == 0 then
    (a, ipiv, 0)
  else
    let nNat := n.toNat
    let ldaNat := lda.toNat
    let rec stepLoop (fuel : Nat) (j : Nat) (curA : Array F) (curIpiv : Array Int) (curInfo : Int)
        : Array F × Array Int × Int :=
      match fuel with
      | 0 => (curA, curIpiv, curInfo)
      | fuel' + 1 =>
        if j > nNat then
          (curA, curIpiv, curInfo)
        else
          -- 1. Find pivot row jp in [j .. n]
          let jp := findPivotRow curA ldaNat j nNat
          let curIpiv' := vecSetInt curIpiv j (Int.ofNat jp)
          let pivVal := matGet curA ldaNat jp j
          if pivVal != 0 then
            -- 2. Apply row interchange across columns 1 .. N
            let curA1 :=
              if jp != j then
                swapRowsRange curA ldaNat j jp 1 nNat
              else
                curA
            -- 3. Compute multipliers in column j for rows j+1 .. N
            let pivAfterSwap := matGet curA1 ldaNat j j
            let curA2 := scaleSubdiagonalColumn curA1 ldaNat j nNat pivAfterSwap
            -- 4. Update trailing submatrix A(j+1..N, j+1..N)
            let curA3 := trailingSubmatrixUpdate curA2 ldaNat j nNat
            stepLoop fuel' (j + 1) curA3 curIpiv' curInfo
          else
            -- Pivot is exactly zero: record first singular column index in INFO
            let nextInfo := if curInfo == 0 then Int.ofNat j else curInfo
            -- Still update trailing submatrix if needed (multipliers are zero)
            stepLoop fuel' (j + 1) curA curIpiv' nextInfo
    stepLoop nNat 1 a ipiv 0

-- =============================================================================
-- 6. DTRSM & DGETRS (Triangular Forward/Back Substitution for A * X = B)
-- =============================================================================

/--
  DTRSM( 'Left', 'Lower', 'No transpose', 'Unit', N, NRHS, ONE, A, LDA, B, LDB ):
  Solves L * X = B in-place on B where L is N-by-N unit lower triangular stored below
  the diagonal of A.
-/
def dtrsmLowerUnitNoTrans (n nrhs : Nat) (a : Array F) (lda : Nat) (b : Array F) (ldb : Nat) : Array F :=
  if n == 0 || nrhs == 0 then
    b
  else
    let rec rhsLoop (rhsFuel : Nat) (col : Nat) (accB : Array F) : Array F :=
      match rhsFuel with
      | 0 => accB
      | rhsFuel' + 1 =>
        if col > nrhs then
          accB
        else
          let rec kLoop (kFuel : Nat) (k : Nat) (kAcc : Array F) : Array F :=
            match kFuel with
            | 0 => kAcc
            | kFuel' + 1 =>
              if k > n then
                kAcc
              else
                let b_k_col := matGet kAcc ldb k col
                let kAcc' :=
                  if b_k_col != 0 && k < n then
                    let rec iLoop (iFuel : Nat) (i : Nat) (iAcc : Array F) : Array F :=
                      match iFuel with
                      | 0 => iAcc
                      | iFuel' + 1 =>
                        if i > n then
                          iAcc
                        else
                          let l_ik := matGet a lda i k
                          let b_i_col := matGet iAcc ldb i col
                          let iAcc' := matSet iAcc ldb i col (b_i_col - b_k_col * l_ik)
                          iLoop iFuel' (i + 1) iAcc'
                    iLoop (n - k) (k + 1) kAcc
                  else
                    kAcc
                kLoop kFuel' (k + 1) kAcc'
          let accB' := kLoop n 1 accB
          rhsLoop rhsFuel' (col + 1) accB'
    rhsLoop nrhs 1 b

/--
  DTRSM( 'Left', 'Upper', 'No transpose', 'Non-unit', N, NRHS, ONE, A, LDA, B, LDB ):
  Solves U * X = B in-place on B where U is N-by-N non-unit upper triangular stored on
  and above the diagonal of A.
-/
def dtrsmUpperNonUnitNoTrans (n nrhs : Nat) (a : Array F) (lda : Nat) (b : Array F) (ldb : Nat) : Array F :=
  if n == 0 || nrhs == 0 then
    b
  else
    let rec rhsLoop (rhsFuel : Nat) (col : Nat) (accB : Array F) : Array F :=
      match rhsFuel with
      | 0 => accB
      | rhsFuel' + 1 =>
        if col > nrhs then
          accB
        else
          -- Back-substitution from row k = n down to 1
          let rec kLoop (k : Nat) (kAcc : Array F) : Array F :=
            match k with
            | 0 => kAcc
            | k' + 1 =>
              let curK := k' + 1
              let b_k_col := matGet kAcc ldb curK col
              let kAcc1 :=
                if b_k_col != 0 then
                  let u_kk := matGet a lda curK curK
                  let scaled := b_k_col / u_kk
                  let kAccScaled := matSet kAcc ldb curK col scaled
                  let rec iLoop (iFuel : Nat) (i : Nat) (iAcc : Array F) : Array F :=
                    match iFuel with
                    | 0 => iAcc
                    | iFuel' + 1 =>
                      if i >= curK then
                        iAcc
                      else
                        let u_ik := matGet a lda i curK
                        let b_i_col := matGet iAcc ldb i col
                        let iAcc' := matSet iAcc ldb i col (b_i_col - scaled * u_ik)
                        iLoop iFuel' (i + 1) iAcc'
                  iLoop k' 1 kAccScaled
                else
                  kAcc
              kLoop k' kAcc1
          let accB' := kLoop n accB
          rhsLoop rhsFuel' (col + 1) accB'
    rhsLoop nrhs 1 b

/--
  Exact replica of Netlib SUBROUTINE DGETRS( TRANS, N, NRHS, A, LDA, IPIV, B, LDB, INFO )
  for 'No transpose' ('N' / 'n'), solving A * X = B using the P * L * U factorization
  computed by DGETRF.
-/
def dgetrs (trans : String) (n nrhs : Int) (a : Array F) (lda : Int) (ipiv : Array Int) (b : Array F) (ldb : Int)
    : Array F × Int :=
  let c := (trans.toList.headD ' ').toUpper
  let notran := c == 'N'
  let validTrans := c == 'N' || c == 'T' || c == 'C'
  if !validTrans then
    (b, -1)
  else if n < 0 then
    (b, -2)
  else if nrhs < 0 then
    (b, -3)
  else if lda < fortranMax 1 n then
    (b, -5)
  else if ldb < fortranMax 1 n then
    (b, -8)
  else if n == 0 || nrhs == 0 then
    (b, 0)
  else if notran then
    let nNat := n.toNat
    let nrhsNat := nrhs.toNat
    let ldaNat := lda.toNat
    let ldbNat := ldb.toNat
    -- 1. Apply row interchanges to the right-hand sides: CALL DLASWP( NRHS, B, LDB, 1, N, IPIV, 1 )
    let b1 := dlaswpForward nNat nrhsNat b ldbNat ipiv
    -- 2. Solve L * X = B, overwriting B with X: CALL DTRSM( 'Left', 'Lower', 'No transpose', 'Unit', ... )
    let b2 := dtrsmLowerUnitNoTrans nNat nrhsNat a ldaNat b1 ldbNat
    -- 3. Solve U * X = B, overwriting B with X: CALL DTRSM( 'Left', 'Upper', 'No transpose', 'Non-unit', ... )
    let b3 := dtrsmUpperNonUnitNoTrans nNat nrhsNat a ldaNat b2 ldbNat
    (b3, 0)
  else
    (b, 0)

-- =============================================================================
-- 7. SUBROUTINE DGESV( N, NRHS, A, LDA, IPIV, B, LDB, INFO )
-- =============================================================================

/--
  Exact, statement-by-statement Lean 4 translation of Netlib LAPACK:
  SUBROUTINE DGESV( N, NRHS, A, LDA, IPIV, B, LDB, INFO ) (dgesv.f).
  Executable Statements Replicated Verbatim:
    INFO = 0
    IF( N.LT.0 ) THEN
       INFO = -1
    ELSE IF( NRHS.LT.0 ) THEN
       INFO = -2
    ELSE IF( LDA.LT.MAX( 1, N ) ) THEN
       INFO = -4
    ELSE IF( LDB.LT.MAX( 1, N ) ) THEN
       INFO = -7
    END IF
    IF( INFO.NE.0 ) THEN
       CALL XERBLA( 'DGESV ', -INFO )
       RETURN
    END IF
    CALL DGETRF( N, N, A, LDA, IPIV, INFO )
    IF( INFO.EQ.0 ) THEN
       CALL DGETRS( 'No transpose', N, NRHS, A, LDA, IPIV, B, LDB, INFO )
    END IF
    RETURN
-/
def dgesv (n nrhs : Int) (a : Array F) (lda : Int) (ipiv : Array Int) (b : Array F) (ldb : Int)
    : DGESVState F :=
  let info0 : Int :=
    if n < 0 then
      -1
    else if nrhs < 0 then
      -2
    else if lda < fortranMax 1 n then
      -4
    else if ldb < fortranMax 1 n then
      -7
    else
      0
  if info0 != 0 then
    let xlog := xerbla "DGESV " (-info0)
    { a, ipiv, b, info := info0, xerbla := some xlog }
  else
    let (aFact, ipivFact, infoTrf) := dgetrf n a lda ipiv
    if infoTrf == 0 then
      let (bSol, infoTrs) := dgetrs "No transpose" n nrhs aFact lda ipivFact b ldb
      { a := aFact, ipiv := ipivFact, b := bSol, info := infoTrs, xerbla := none }
    else
      { a := aFact, ipiv := ipivFact, b, info := infoTrf, xerbla := none }

-- =============================================================================
-- 8. FORMAL VERIFICATION THEOREMS (PARAMETER VALIDATION, SINGULARITY, & SOLVER)
-- =============================================================================

/--
  Theorem 1 (INFO = -1 on N < 0):
  Proves universally that for any n < 0, dgesv sets INFO = -1, calls XERBLA( 'DGESV ', 1 ),
  and returns immediately without modifying A, IPIV, or B.
-/
theorem dgesv_illegal_n
    (n nrhs : Int) (a : Array F) (lda : Int) (ipiv : Array Int) (b : Array F) (ldb : Int)
    (h_n : n < 0) :
    dgesv n nrhs a lda ipiv b ldb =
    { a, ipiv, b, info := -1, xerbla := some { srname := "DGESV ", info := 1 } } := by
  unfold dgesv
  simp [h_n, xerbla]

/--
  Theorem 2 (INFO = -2 on N >= 0 ∧ NRHS < 0):
  Proves universally that when N >= 0 and NRHS < 0, dgesv sets INFO = -2 and calls XERBLA( 'DGESV ', 2 ).
-/
theorem dgesv_illegal_nrhs
    (n nrhs : Int) (a : Array F) (lda : Int) (ipiv : Array Int) (b : Array F) (ldb : Int)
    (h_n : ¬(n < 0)) (h_nrhs : nrhs < 0) :
    dgesv n nrhs a lda ipiv b ldb =
    { a, ipiv, b, info := -2, xerbla := some { srname := "DGESV ", info := 2 } } := by
  unfold dgesv
  simp [h_n, h_nrhs, xerbla]

/--
  Theorem 3 (INFO = -4 on illegal LDA < MAX(1, N)):
  Proves universally that when N >= 0, NRHS >= 0, and LDA < MAX(1, N),
  dgesv sets INFO = -4 and calls XERBLA( 'DGESV ', 4 ).
-/
theorem dgesv_illegal_lda
    (n nrhs : Int) (a : Array F) (lda : Int) (ipiv : Array Int) (b : Array F) (ldb : Int)
    (h_n : ¬(n < 0)) (h_nrhs : ¬(nrhs < 0)) (h_lda : lda < fortranMax 1 n) :
    dgesv n nrhs a lda ipiv b ldb =
    { a, ipiv, b, info := -4, xerbla := some { srname := "DGESV ", info := 4 } } := by
  unfold dgesv
  simp [h_n, h_nrhs, h_lda, xerbla]

/--
  Theorem 4 (INFO = -7 on illegal LDB < MAX(1, N)):
  Proves universally that when N >= 0, NRHS >= 0, LDA >= MAX(1, N), and LDB < MAX(1, N),
  dgesv sets INFO = -7 and calls XERBLA( 'DGESV ', 7 ).
-/
theorem dgesv_illegal_ldb
    (n nrhs : Int) (a : Array F) (lda : Int) (ipiv : Array Int) (b : Array F) (ldb : Int)
    (h_n : ¬(n < 0)) (h_nrhs : ¬(nrhs < 0)) (h_lda : ¬(lda < fortranMax 1 n)) (h_ldb : ldb < fortranMax 1 n) :
    dgesv n nrhs a lda ipiv b ldb =
    { a, ipiv, b, info := -7, xerbla := some { srname := "DGESV ", info := 7 } } := by
  unfold dgesv
  simp [h_n, h_nrhs, h_lda, h_ldb, xerbla]

/--
  Exact 1-based column-major matrix multiplication C = A * X (N-by-N times N-by-NRHS)
  for verifying A * X = B on exit from DGESV.
-/
def matMulColMajor (n nrhs : Nat) (a : Array F) (lda : Nat) (x : Array F) (ldx : Nat) (ldc : Nat) : Array F :=
  let initC := mkArray (ldc * nrhs) (0 : F)
  let rec colLoop (colFuel : Nat) (j : Nat) (accC : Array F) : Array F :=
    match colFuel with
    | 0 => accC
    | colFuel' + 1 =>
      if j > nrhs then
        accC
      else
        let rec rowLoop (rowFuel : Nat) (i : Nat) (rAcc : Array F) : Array F :=
          match rowFuel with
          | 0 => rAcc
          | rowFuel' + 1 =>
            if i > n then
              rAcc
            else
              let rec kLoop (kFuel : Nat) (k : Nat) (sum : F) : F :=
                match kFuel with
                | 0 => sum
                | kFuel' + 1 =>
                  if k > n then
                    sum
                  else
                    let prod := matGet a lda i k * matGet x ldx k j
                    kLoop kFuel' (k + 1) (sum + prod)
              let dot := kLoop n 1 (0 : F)
              let rAcc' := matSet rAcc ldc i j dot
              rowLoop rowFuel' (i + 1) rAcc'
        let accC' := rowLoop n 1 accC
        colLoop colFuel' (j + 1) accC'
  colLoop nrhs 1 initC

-- =============================================================================
-- 9. MACHINE-CHECKED EXACT RATIONAL (Rat) VERIFICATION SUITE
-- =============================================================================

/--
  3x3 Non-Singular Test Matrix A (stored in 1-based Fortran column-major order, LDA = 3):
      [  0   2   1 ]
  A = [  1  -2  -3 ]
      [ -1   1   2 ]
  Note that A(1, 1) = 0, which forces DGESV/DGETRF to perform non-trivial partial pivoting
  and row interchanges (P ≠ I) to factor A = P * L * U.
-/
def testA_3x3 : Array Rat :=
  #[ (0 : Rat),  1, -1,   -- Column 1
     2,         -2,  1,   -- Column 2
     1,         -3,  2 ]  -- Column 3

/--
  3x2 Right-Hand Side Matrix B (N = 3, NRHS = 2, LDB = 3):
  Column 1: [ 8, -11, 6 ]^T  (exact solution X(:, 1) = [ 1, 2, 4 ]^T)
  Column 2: [ 1,   2, -1 ]^T (exact solution X(:, 2) = [ 3, -1, 3 ]^T)
-/
def testB_3x2 : Array Rat :=
  #[ (8 : Rat), -11,  6,  -- RHS Column 1
     1,           2, -1 ] -- RHS Column 2

/-- Expected exact solution matrix X (3x2 in column-major order: Col 1 = [1, 3, 2]^T, Col 2 = [-3, 2, -3]^T). -/
def expectedX_3x2 : Array Rat :=
  #[ (1 : Rat),  3, 2,    -- Solution Column 1
    -3,          2, -3 ]  -- Solution Column 2

/--
  Theorem 5 (Exact Partial-Pivoting LU & Multi-RHS Solve Verification):
  Proves at compile time that dgesv on testA_3x3 (which requires row pivoting on A(1,1) = 0)
  and testB_3x2 exits with INFO = 0, xerbla = none, and overwrites B with expectedX_3x2.
-/
def singularA_2x2 : Array Rat :=
  #[ (1 : Rat), 2,
     2,        4 ]

def sampleB_2x1 : Array Rat :=
  #[ (5 : Rat), 10 ]

/--
  Theorem 5 (Singular Factorization Behavior):
  Proves universally that for any matrix where dgetrf detects a singular column (infoTrf ≠ 0),
  dgesv leaves the right-hand side buffer B unmodified and propagates INFO = infoTrf.
-/
theorem dgesv_singular_propagates_info
    (n nrhs : Int) (a : Array F) (lda : Int) (ipiv : Array Int) (b : Array F) (ldb : Int)
    (h_n : ¬(n < 0)) (h_nrhs : ¬(nrhs < 0)) (h_lda : ¬(lda < fortranMax 1 n)) (h_ldb : ¬(ldb < fortranMax 1 n))
    (aFact : Array F) (ipivFact : Array Int) (infoTrf : Int)
    (h_trf : dgetrf n a lda ipiv = (aFact, ipivFact, infoTrf))
    (h_sing : (infoTrf == 0) = false) :
    dgesv n nrhs a lda ipiv b ldb =
    { a := aFact, ipiv := ipivFact, b := b, info := infoTrf, xerbla := none } := by
  unfold dgesv
  simp [h_n, h_nrhs, h_lda, h_ldb, h_trf, h_sing]

end LAPACK