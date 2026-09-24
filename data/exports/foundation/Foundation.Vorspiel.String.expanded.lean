module


-- @@ L3-3 verbatim
@[expose] public section


-- @@ L5-5 verbatim
namespace String


-- @@ L7-9 verbatim
def vecToStr : ∀ {n}, (Fin n → String) → String
  | 0,     _ => ""
  | n + 1, s => if n = 0 then s 0 else s 0 ++ ", " ++ @vecToStr n (fun i => s (Fin.succ i))


-- @@ L11-11 verbatim
end String


-- @@ L13-13 verbatim
end
