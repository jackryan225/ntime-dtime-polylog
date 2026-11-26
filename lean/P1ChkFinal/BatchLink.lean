import P1ChkFinal.Skeleton
import P1Batch.Statement

/-! `BatchHyp` is discharged by the batch lane's theorem `P1Batch.batch_lookup` (job batch-11, standard axioms). -/

namespace P1ChkFinal

theorem batchHyp : BatchHyp := P1Batch.batch_lookup

end P1ChkFinal
