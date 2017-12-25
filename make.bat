:: ###################################################
:: Miking is licensed under the MIT license.
:: Copyright (C) David Broman. See file LICENSE.txt
::
:: To make the build system platform independent,
:: all scripts are done in Ocaml instead of being
:: dependent on Make.
:: ###################################################

@ocaml build\build.ml %1 %2 %3
