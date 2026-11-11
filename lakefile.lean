import Lake
open Lake DSL

package «lean_4_translations» where
  moreLeanArgs := #["-DautoImplicit=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

@[default_target]
lean_lib «AGCBlockTwoReplication» where
  roots := #[`AGCBlockTwoReplication]

@[default_target]
lean_lib «Magnetic_Digital_Elements_1964» where
  roots := #[`Magnetic_Digital_Elements_1964]

@[default_target]
lean_lib «Setun_1960» where
  roots := #[`Setun_1960]

@[default_target]
lean_lib «Setun70_1971» where
  roots := #[`Setun70_1971]

@[default_target]
lean_lib «Setun_Minsk22_Dushanbe_1971» where
  roots := #[`Setun_Minsk22_Dushanbe_1971]

@[default_target]
lean_lib «intel4004» where
  roots := #[`intel4004]

@[default_target]
lean_lib «CrossLayerBridge» where
  roots := #[`CrossLayerBridge]

@[default_target]
lean_lib «executive_agc» where
  roots := #[`executive_agc]

@[default_target]
lean_lib «interpreter_agc» where
  roots := #[`interpreter_agc]
