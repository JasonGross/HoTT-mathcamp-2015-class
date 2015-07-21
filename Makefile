V = 0

SILENCE_COQC_0 = @echo "COQC $<"; #
SILENCE_COQC_1 =
SILENCE_COQC = $(SILENCE_COQC_$(V))

SILENCE_COQDEP_0 = @echo "COQDEP $<"; #
SILENCE_COQDEP_1 =
SILENCE_COQDEP = $(SILENCE_COQDEP_$(V))

SILENCE_OCAMLC_0 = @echo "OCAMLC $<"; #
SILENCE_OCAMLC_1 =
SILENCE_OCAMLC = $(SILENCE_OCAMLC_$(V))

SILENCE_OCAMLDEP_0 = @echo "OCAMLDEP $<"; #
SILENCE_OCAMLDEP_1 =
SILENCE_OCAMLDEP = $(SILENCE_OCAMLDEP_$(V))

SILENCE_OCAMLOPT_0 = @echo "OCAMLOPT $<"; #
SILENCE_OCAMLOPT_1 =
SILENCE_OCAMLOPT = $(SILENCE_OCAMLOPT_$(V))

Q_0 := @
Q_1 :=
Q = $(Q_$(V))

VECHO_0 := @echo
VECHO_1 := @true
VECHO = $(VECHO_$(V))

TIMED=
TIMECMD=
STDTIME?=/usr/bin/time -f "$* (real: %e, user: %U, sys: %S, mem: %M ko)"
TIMER=$(if $(TIMED), $(STDTIME), $(TIMECMD))

containing = $(foreach v,$2,$(if $(findstring $1,$v),$v))
not-containing = $(foreach v,$2,$(if $(findstring $1,$v),,$v))

HASNATDYNLINK = true

.PHONY: all clean download-packages

FAST_TARGETS := clean archclean Makefile.coq HoTT-syllabus-Jason.pdf HoTT-homework-day-1.pdf

EXERCISES = \
	exercises_and_homework_day_2 \
	exercises_and_homework_day_3 \
	exercises_and_homework_day_4_student \
	exercises_and_homework_day_4_teacher_answer_key \
	exercises_and_homework_day_5_teacher_answer_key

all: HoTT-syllabus-Jason.pdf HoTT-homework-day-1.pdf \
	$(addsuffix .pdf,$(EXERCISES)) \
	$(addsuffix .html,$(EXERCISES))

COQDOCFLAGS?=-interpolate -utf8 -s

%.pdf: %.tex
	@ pdflatex -synctex=1 $<
	@ pdflatex -synctex=1 $<

$(addsuffix .tex,$(EXERCISES)) : %.tex : %.v %.vo
	$(COQDOC) $(COQDOCFLAGS) -latex $(COQDOCLIBS) -o $@ $<

$(addsuffix .html,$(EXERCISES)) : %.html : %.v %.vo
	$(COQDOC) $(COQDOCFLAGS) -html $(COQDOCLIBS) -d . $<
	sed s'/background-color: #90bdff;/background-color: aliceblue;/g' -i coqdoc.css

Makefile.coq: Makefile _CoqProject
	$(VECHO) "COQ_MAKEFILE -f _CoqProject > $@"
	$(Q)$(COQBIN)coq_makefile COQC = "\$$(SILENCE_COQC)\$$(TIMER) \"\$$(COQBIN)coqc\"" COQDEP = "\$$(SILENCE_COQDEP)\"\$$(COQBIN)coqdep\" -c" -f _CoqProject | sed s'/^\(-include.*\)$$/ifneq ($$(filter-out $(FAST_TARGETS),$$(MAKECMDGOALS)),)~\1~else~ifeq ($$(MAKECMDGOALS),)~\1~endif~endif/g' | tr '~' '\n' | sed s'/^clean:$$/clean-old::/g' | sed s'/^Makefile: /Makefile-old: /g' > $@

-include Makefile.coq

download-packages::
	wget -N http://mirrors.ctan.org/macros/latex/contrib/pageslts/pageslts.dtx
	tex pageslts.dtx
	wget -N http://www.ctan.org/tex-archive/macros/latex/contrib/oberdiek/atveryend.dtx
	tex atveryend.dtx
	wget -N http://mirrors.ctan.org/macros/latex/contrib/undolabl/undolabl.dtx
	tex undolabl.dtx
	for i in atveryend rerunfilecheck kvoptions ltxcmds; do \
		wget -N http://www.ctan.org/tex-archive/macros/latex/contrib/oberdiek/$$i.dtx; \
		tex $$i.dtx; \
	done

clean::
	$(VECHO) "RM *.CMO *.CMI *.CMA"
	$(Q)rm -f $(ALLCMOFILES) $(CMIFILES) $(CMAFILES)
	$(VECHO) "RM *.CMX *.CMXS *.CMXA *.O *.A"
	$(Q)rm -f $(ALLCMOFILES:.cmo=.cmx) $(CMXAFILES) $(CMXSFILES) $(ALLCMOFILES:.cmo=.o) $(CMXAFILES:.cmxa=.a)
	$(VECHO) "RM *.ML.D *.MLI.D *.ML4.D *.MLLIB.D"
	$(Q)rm -f $(addsuffix .d,$(MLFILES) $(MLIFILES) $(ML4FILES) $(MLLIBFILES) $(MLPACKFILES))
	$(VECHO) "RM *.VO *.VI *.G *.V.D *.V.BEAUTIFIED *.V.OLD"
	$(Q)rm -f $(VOFILES) $(VIFILES) $(GFILES) $(VFILES:.v=.v.d) $(VFILES:=.beautified) $(VFILES:=.old)
	$(VECHO) "RM *.PS *.PDF *.GLOB *.TEX *.G.TEX"
	$(Q)rm -f all.ps all-gal.ps all.pdf all-gal.pdf all.glob $(VFILES:.v=.glob) $(VFILES:.v=.tex) $(VFILES:.v=.g.tex) all-mli.tex $(VFILES:.v=.html) $(VFILES:.v=.pdf) *.synctex.gz
	- rm -rf html mlihtml
	rm -f Makefile.coq .depend
	rm -f HoTT-syllabus-Jason.pdf HoTT-homework-day-1.pdf
	@ rm -f *.aux *.out *.nav *.toc *.vrb *.pdf *.snm *.log *.bbl *.blg
