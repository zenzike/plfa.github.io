---
layout: page
title: Getting Started
permalink: /GettingStarted/
---

[![Build Status](https://travis-ci.org/plfa/plfa.github.io.svg?branch=dev)](https://travis-ci.org/plfa/plfa.github.io)
[![Agda](https://img.shields.io/badge/agda-2.5.4.2-blue.svg)](https://github.com/agda/agda/releases/tag/v2.5.4.2)
[![agda-stdlib](https://img.shields.io/badge/agda--stdlib-0.17-blue.svg)](https://github.com/agda/agda-stdlib/releases/tag/v0.17)
[![agda2html](https://img.shields.io/badge/agda2html-0.2.3.0-blue.svg)](https://github.com/wenkokke/agda2html/releases/tag/v0.2.3.0)


# Getting Started with PLFA

There are several tools you need to work with PLFA:

  - [Agda](https://agda.readthedocs.io/en/v2.5.4.2/getting-started/installation.html)
  - [Agda standard library](https://github.com/agda/agda-stdlib/tree/5819a4dd9c965296224944f05b1481805649bdc2)

For most of the tools, you can simply follow their respective build instructions.
We list the versions of our dependencies on the badges above.

You can get the latest version of Programming Language Foundations in Agda from Github, 
either by cloning the repository, 
or by downloading [the zip archive](https://github.com/plfa/plfa.github.io/archive/dev.zip):

    git clone https://github.com/plfa/plfa.github.io 

Finally, we need to let Agda know where to find the standard library.
For this, you can follow the instructions [here](https://agda.readthedocs.io/en/v2.5.4.2/tools/package-system.html#example-using-the-standard-library).

It is possible to set up PLFA as an Agda library as well.
If you are trying to complete the exercises found in the `tspl` folder, or otherwise want to import modules from the book, you need to do this.
To do so, add the path to `plfa.agda-lib` to `~/.agda/libraries` and add `plfa` to `~/.agda/defaults`, both on lines of their own.


# Building the book

To build and host a local copy of the book, there are several tools you need *in addition to those listed above*:

  - [agda2html](https://github.com/wenkokke/agda2html)
  - [Ruby](https://www.ruby-lang.org/en/documentation/installation/)
  - [Bundler](https://bundler.io/#getting-started)
  
For most of the tools, you can simply follow their respective build instructions.
Most recent versions of Ruby should work.

We advise installing agda2html using [Stack](https://docs.haskellstack.org/en/stable/README/):

    git clone https://github.com/wenkokke/agda2html.git
    cd agda2html
    stack install 

Once you have installed these tools, you can build the book from source:

    make build
    
You can host your copy of the book locally by running:

    make serve
    
The Makefile offers more than just these options:

    make                      (see make test)
    make build                (builds lagda->markdown and the website)
    make build-offline        (builds lagda->markdown and the website offline)
    make build-incremental    (builds lagda->markdown and the website incrementally)
    make test                 (checks all links are valid)
    make test-offline         (checks all links are valid offline)
    make serve                (starts the server)
    make server-start         (starts the server in detached mode)
    make server-stop          (stops the server, uses pkill)
    make clean                (removes all ~unnecessary~ generated files)
    make clobber              (removes all generated files)

If you simply wish to have a local copy of the book, e.g. for offline reading,
but don't care about editing and rebuilding the book, you can grab a copy of the
[master branch](https://github.com/plfa/plfa.github.io/archive/master.zip),
which is automatically built using Travis. You will still need Ruby and Bundler
to host the book (see above). To host the book this way, download a copy of the
[master branch](https://github.com/plfa/plfa.github.io/archive/master.zip),
unzip, and from within the directory run

    bundle install
    bundle exec jekyll serve

## GNU sed and macOS

The version of sed that ships with macOS is not fully compatible with the GNU sed.
Therefore, you may get errors such as:
```
sed: 1: "out/plfa/Bisimulation.md": invalid command code o
```
You can fix this error by installing a GNU compatible version of sed, e.g. using [Homebrew](https://brew.sh/):
```
brew install gnu-sed --with-default-names
```

## Updating `agda2html`

Sometimes we have to update agda2html. 
To update your local copy, run the following commands from your clone of the
agda2html repository, or simply follow the installation instructions again:

    git pull
    stack install


## Unicode characters

If you're having trouble typing the Unicode characters into Emacs, the end of
each chapter should provide a list of the unicode characters introduced in that
chapter. For a full list of supported characters, see
[agda-input.el](https://github.com/agda/agda/blob/master/src/data/emacs-mode/agda-input.el#L194).


## Using `agda-mode`

    ?            hole
    {!...!}      hole with contents
    C-c C-l      load buffer

Command to give when in a hole:

    C-c C-c x    split on variable x
    C-c C-space  fill in hole
    C-c C-r      refine with constructor
    C-c C-a      automatically fill in hole
    C-c C-,      Goal type and context
    C-c C-.      Goal type, context, and inferred type

See
[the emacs-mode docs](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)
for more details.

If you want to see messages beside rather than below your Agda code,
you can do the following: 

  - Load your Agda file and do `C-c C-l`;
  - type `C-x 1` to get only your Agda file showing; 
  - type `C-x 3` to split the window horizontally;
  - move your cursor to the right-hand half of your frame; 
  - type `C-x b` and switch to the buffer called "Agda information"
  
Now, error messages from Agda will appear next to your file, rather than
squished beneath it.


## Fonts in Emacs

It is recommended that you add the following to the end of your emacs
configuration file at `~/.emacs`, if you have the mentioned fonts available:

``` elisp
;; Setting up Fonts for use with Agda/PLFA
;;
;; default to DejaVu Sans Mono, 
(set-face-attribute 'default nil
		    :family "DejaVu Sans Mono"
		    :height 120
		    :weight 'normal
		    :width  'normal)

;; fix \:
(set-fontset-font "fontset-default"
		  (cons (decode-char 'ucs #x2982)
			(decode-char 'ucs #x2982))
		  "STIX")
```


## Markdown

The book is written in
[Kramdown Markdown](https://kramdown.gettalong.org/syntax.html).


## Travis Continuous Integration

You can view the build history of PLFA at [travis-ci.org](https://travis-ci.org/plfa/plfa.github.io).
