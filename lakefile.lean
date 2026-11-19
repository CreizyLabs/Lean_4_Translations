import Lake
open Lake DSL

package «lean_4_translations» where
  moreLeanArgs := #["-DautoImplicit=false"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

@[default_target]
lean_lib «ApolloMission» where
  roots := #[
    `ApolloMission.LEM_GEOMETRY,
    `ApolloMission.PLANETARY_INERTIAL_ORIENTATION,
    `ApolloMission.THE_LUNAR_LANDING,
    `ApolloMission.AGCBlockTwoReplication,
    `ApolloMission.executive_agc,
    `ApolloMission.interpreter_agc
  ]

@[default_target]
lean_lib «StoryOfMel» where
  roots := #[
    `StoryOfMel.MelLGP30,
    `StoryOfMel.BkjckTape,
    `StoryOfMel.NatherStoryOfMel
  ]

@[default_target]
lean_lib «Setun» where
  roots := #[
    `Setun.Setun_1960,
    `Setun.Setun70_1971,
    `Setun.Setun_Minsk22_Dushanbe_1971,
    `Setun.Magnetic_Digital_Elements_1964,
    `Setun.CrossLayerBridge
  ]

@[default_target]
lean_lib «Intel4004» where
  roots := #[`Intel4004.intel4004]

@[default_target]
lean_lib «LAPACK» where
  roots := #[`LAPACK.DGESV]

@[default_target]
lean_lib «TempleOS» where
  roots := #[`TempleOS.TempleOS]

@[default_target]
lean_lib «ColdWarDefense» where
  roots := #[
    `ColdWarDefense.ImpCodeResurrection,
    `ColdWarDefense.ImpHardware,
    `ColdWarDefense.SageProgramming,
    `ColdWarDefense.SkipjackKEA
  ]
