default: native

clean:
	ocamlbuild -clean

native:
	ocamlbuild -use-menhir principia.native

byte:
	ocamlbuild -use-menhir principia.byte -tag 'debug'