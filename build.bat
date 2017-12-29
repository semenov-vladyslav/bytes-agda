@echo off

set PATH=C:\Program Files (x86)\CMake\bin\;C:\Users\Vlad\AppData\Roaming\local\bin\;C:\usr\ghc8\bin\;C:\usr\ghc8\mingw\bin\;C:\Windows\System32\
set PATH=%PATH%;C:\MinGW\msys\1.0\bin\

agda -c app/binio.agda --compile-dir ../.agda-ghc 
rem 2>&1 >build.log
