import NpTetris.Mino.KMino
import NpTetris.Mino.LekMino

instance {k} : Fintype (KShape k) where
elems := sorry
complete := sorry

instance {k} : Fintype (LeKShape k) := sorry
