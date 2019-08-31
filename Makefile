TAGS=-tags "optimize(3)" #debug" 

eff:
	ocamlbuild -package qcheck -cflags -w,a $(TAGS) src/env.cma
	ocamlbuild -package qcheck -cflags -w,a $(TAGS) src/ast.cma
	ocamlbuild -package qcheck -cflags -w,a $(TAGS) src/tcheck.cma
	ocamlbuild -package qcheck -cflags -w,a $(TAGS) src/generator.cma
	ocamlbuild -package qcheck -cflags -w,a $(TAGS) src/shrinker.cma
	ocamlbuild -package qcheck -cflags -w,a $(TAGS) src/efftester.cma
	ocamlbuild -package qcheck -package str -cflags -w,a $(TAGS) src/effmain.byte
	ocamlbuild -package qcheck -package str -cflags -w,a $(TAGS) src/effmain.native


stat:
	ocamlbuild -package qcheck src/effstat.native

clean:
	ocamlbuild -clean
	rm -f *~
	rm -f testdir/test.{ml,o,cmi,cmo,cmx} testdir/{byte,native,byte.out,native.out}
