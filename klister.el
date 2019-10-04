;;; klister.el --- A major mode for editing Klister files  -*- lexical-binding: t; -*-

;; Copyright (C) 2019, Langston Barrett

;; Author: Langston Barrett <langston.barrett@gmail.com>
;; Keywords: languages
;; Package-Requires: ((emacs "24.4") (cl-lib "0.5"))
;; Package-Version: 0.5
;; Homepage: https://github.com/langston-barrett/klister-mode

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is a major mode for editing Klister files.

;;; Code:

(require 'compile)
(require 'cl-lib)

;;; Configuration

(defgroup klister '()
  "Klister"
  :group 'languages
  :tag "Klister")

(defface klister-keyword-face
  '((t (:inherit font-lock-keyword-face)))
  "How to highlight Klister keywords."
  :group 'klister)

(defface klister-operator-face
  '((t (:inherit font-lock-keyword-face)))
  "How to highlight Klister build-in operators."
  :group 'klister)

;;; Highlighting

(defconst klister-keywords
  '(;; Declarations
    "#lang"
    "meta"
    "export"
    "import"
    "examples"
    "define"
    "define-macros"
    ;; Expressions
    "oops"
    "lambda"
    "#%app"
    "pure"
    "syntax-error"
    "send-signal"
    "wait-signal"
    "bound-identifier=?"
    "free-identifier=?"
    "quote"
    "if"
    "ident"
    "ident-syntax"
    "empty-list-syntax"
    "cons-list-syntax"
    "vec-syntax"
    "syntax-case"
    "let-syntax"))

(defvar klister--keyword-regexp
  (regexp-opt klister-keywords 'words)
  "Regular expression for Klister keyword highlighting.")

(defconst klister-operators
  '(">>=")
  "Operators to highlight in Klister.")

(defvar klister--operator-regexp
  (regexp-opt klister-operators)
  "Regular expression for Klister keyword highlighting.")

(defvar klister-font-lock-defaults
  `(((,klister--keyword-regexp . 'klister-keyword-face)
     (,klister--operator-regexp . 'klister-operator-face)
     )
    nil nil nil
    (font-lock-extend-after-change-region-function . klister--extend-after-change-region-function))
  "Highlighting instructions for Klister.")

;;; Default keybindings

(defvar klister-mode-map
  (let ((map (make-sparse-keymap)))
    map)
  "Keymap for Klister mode.")

;;; The mode itself

;;;###autoload
(define-derived-mode klister-mode prog-mode "Klister"
  "A major mode for editing Klister files."
  (setq font-lock-defaults klister-font-lock-defaults)
  (setq font-lock-multiline t)

  ;; Comment syntax
  (setq-local comment-start "-- ")
  (setq-local comment-end ""))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.kl\\'" . klister-mode))

(provide 'klister)
;;; klister.el ends here
