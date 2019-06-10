all: slides.pdf

slides.tex: slides.md
	@pandoc \
		-t beamer $< \
		--standalone \
		--biblatex \
		--slide-level 1 \
		-o $@
	@echo "Compiled $< to $@"

slides.pdf: slides.tex
	@tectonic $<
	@echo "Rendered $< to $@"

clean:
	$(RM) slides.tex slides.pdf

.PHONY: clean
