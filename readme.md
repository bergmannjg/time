# Time package

Port of the [haskell time library](https://github.com/haskell/time) to [Lean 4](https://github.com/leanprover/lean4) (WIP).

Missing modules

* [FormatTime](https://github.com/haskell/time/blob/master/lib/Data/Time/Format/Format/Class.hs)
* [AbsoluteTime](https://github.com/haskell/time/blob/master/lib/Data/Time/Clock/Internal/AbsoluteTime.hs)

## Usage

see [time library doc](https://bergmannjg.github.io/time/book/time.html)

## Build

* reset all: rm -rf build && rm -rf lake-packages
* update: lake update
* create cache: lake exe cache get
* build: lake build
* build docs: lake -Kenv=dev update && lake run buildDocs
* run server: cd build/doc/ && python3 -m http.server
