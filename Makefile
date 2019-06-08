all: slides.pdf

slides.tex: slides.md
	@pandoc \
		-t beamer $< \
		--standalone \
		--biblatex \
		--slide-level 2 \
		-o $@
	@echo 'Compiled $< to $@'

slides.pdf: slides.tex
	tectonic $<

clean:
	$(RM) slides.tex slides.pdf

.PHONY: clean
