CASK_BIN ?= cask
EMACS_BIN ?= emacs
ORGS := $(wildcard *.org)
HTMLS := $(ORGS:.org=.html)
TEXS := $(wildcard *.tex)
PDFS := $(wildcard *.pdf)
CWD := $(shell pwd)
WATCHMAN_BIN ?= $(CWD)/watchman/watchman

all: $(HTMLS) $(PDFS)

%.html: %.org .cask elisp/org-batch.el
	@if [ ! -f ~/.cask/bin/cask ]; then echo "Cask Not Found. Please do 'make install-cask' first"; exit 1; fi
	$(EMACS_BIN) -no-site-file -q --batch -l elisp/org-batch.el --visit $< -f org-html-export-to-html

%.tex: %.org .cask elisp/org-pdf-export.el
	$(EMACS_BIN) -Q --batch --eval "(require 'org)" --eval "(setq org-latex-listings 'minted)" --eval "(setq org-confirm-babel-evaluate nil)" --visit=$< --funcall org-latex-export-to-latex

%.pdf: %.tex
	xelatex --shell-escape $<

.cask: Cask
	@EMACS=$(EMACS_BIN) $(CASK_BIN)
	@touch .cask

clean:
	rm -rf $(HTMLS)

watch-on:
	$(WATCHMAN_BIN) watch $(CWD)
	$(WATCHMAN_BIN) -- trigger $(CWD) org-files '*.org' -- make all

watch-off:
	$(WATCHMAN_BIN) -- trigger-del $(CWD) org-files
	$(WATCHMAN_BIN) watch-del $(CWD)

install-cask:
	curl -fsSkL https://raw.github.com/cask/cask/master/go | python

install-watchman:
	git clone https://github.com/facebook/watchman.git
	cd watchman &&./autogen.sh && ./configure && make

.PHONY: all clean install-cask install-watchman watch-on watch-off
