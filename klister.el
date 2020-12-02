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

(defcustom klister-command "klister"
  "The command to run to execute Klister."
  :type 'string
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
    "list-syntax"
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

;;; Running

(defun klister--compilation-buffer-name-function (_mode)
  "Compute a name for the Klister compilation buffer."
  "*Klister*")

(defun klister-run-file (filename)
  "Run FILENAME in Klister."
  (interactive "fFile to run in Klister: ")
  (let* ((dir (file-name-directory filename))
         (file (file-name-nondirectory filename))
         (command (concat klister-command " run " file))
         ;; Special variables that configure compilation mode
         (compilation-buffer-name-function
          'klister--compilation-buffer-name-function)
         (default-directory dir))
    (let ((compilation-finish-functions (list (lambda (_x) (message "Done!")))))
      (compile command))))

(defun klister-run-buffer (buffer)
  "Run the file from BUFFER in Klister."
  (interactive "bBuffer: ")
  (let ((file (buffer-file-name buffer)))
    (if file
        (progn (when (buffer-modified-p buffer)
                 (when (yes-or-no-p "Buffer modified. Save first? ")
                   (save-buffer buffer)))
               (klister-run-file file))
      (error "Buffer %s has no file" buffer))))

(defun klister-run-current-buffer ()
  "Run the current buffer in Klister."
  (interactive)
  (klister-run-buffer (current-buffer)))

(add-to-list 'compilation-error-regexp-alist-alist
             '(klister-example
               "\\(Example at\\)\\s-+\\(\\([^:]+\\):\\([0-9]+\\).\\([0-9]+\\)-\\([0-9]+\\).\\([0-9]+\\)\\):"
               3 (4 . 6) (5 . 7) 0 2 (1 "compilation-info")))
(cl-pushnew 'klister-example compilation-error-regexp-alist)
(add-to-list 'compilation-error-regexp-alist-alist
             '(klister-type-error
               "\\(Type mismatch at\\)\\s-+\\(\\([^:]+\\):\\([0-9]+\\).\\([0-9]+\\)-\\([0-9]+\\).\\([0-9]+\\)\\)."
               3 (4 . 6) (5 . 7) 0 2 (1 "compilation-error")))
(cl-pushnew 'klister-type-error compilation-error-regexp-alist)

;;; Default keybindings

(defvar klister-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-c") 'klister-run-current-buffer)
    map)
  "Keymap for Klister mode.")

;;; The mode itself

;;;###autoload
(define-derived-mode klister-mode prog-mode "Klister"
  "A major mode for editing Klister files."
  (setq font-lock-defaults klister-font-lock-defaults)
  (setq font-lock-multiline t)

  (setq-local indent-line-function 'indent-relative)

  ;; Comment syntax
  (setq-local comment-start "-- ")
  (setq-local comment-end ""))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.kl\\'" . klister-mode))

(provide 'klister)
;;; klister.el ends here
