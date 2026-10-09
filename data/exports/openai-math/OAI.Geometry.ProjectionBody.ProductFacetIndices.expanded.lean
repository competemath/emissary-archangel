import Mathlib.Data.Fin.Tuple.Basic


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace ProjectionCounterexample


-- @@ L7-11 verbatim
lemma first_succAbove_first (i : Fin 10) (j : Fin 9) :
    (i.castAdd 10).succAbove (j.castAdd 10) = (i.succAbove j).castAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd]
  split_ifs <;> rfl


-- @@ L13-20 verbatim
lemma first_succAbove_second (i : Fin 10) (j : Fin 10) :
    (i.castAdd 10).succAbove (j.natAdd 9) = j.natAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs with h
  · omega
  · simp only [Fin.val_succ, Fin.val_natAdd]
    omega


-- @@ L22-28 verbatim
lemma second_succAbove_first (i : Fin 10) (j : Fin 10) :
    (i.natAdd 10).succAbove (j.castAdd 9) = j.castAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
  split_ifs with h
  · rfl
  · omega


-- @@ L30-34 verbatim
lemma second_succAbove_second (i : Fin 10) (j : Fin 9) :
    (i.natAdd 10).succAbove (j.natAdd 10) = (i.succAbove j).natAdd 10 := by
  ext
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_natAdd]
  split_ifs <;> simp_all only [Fin.val_castSucc, Fin.val_succ, Fin.val_natAdd] <;> omega


-- @@ L36-36 verbatim
end ProjectionCounterexample


-- @@ L38-38 verbatim
end OAI
