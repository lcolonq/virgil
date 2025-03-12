;;; virgil --- DOOM on Bad Apple!! Emacs support package -*- lexical-binding: t; -*-
;;; Commentary:
;;; Code:

(require 'dash)
(require 's)

(defgroup virgil nil
  "Bad Apple!! VM client"
  :group 'applications)

(defcustom v/path "/home/llll/src/virgil/target/debug/virgil"
  "Path to virgil binary"
  :type '(string)
  :group 'virgil)

(defcustom v/debug-process "virgil-debug"
  "Name of process connected to debugger"
  :type '(string)
  :group 'virgil)

(defcustom v/debug-buffer " *virgil-debug*"
  "Name of buffer used to store intermediate debugger data."
  :type '(string)
  :group 'virgil)

(defcustom v/debug-log-buffer " *virgil-debug-log*"
  "Name of buffer used to display debugger diagnostics."
  :type '(string)
  :group 'virgil)

(defcustom v/debug-program-buffer "*virgil-debug-program*"
  "Name of buffer used to display debugger program."
  :type '(string)
  :group 'virgil)

(defface v/debug-ins
  '((t
     :foreground "white"
     ))
  "Face for instruction."
  :group 'virgil)

(defface v/debug-ins-highlight
  '((t
     :foreground "red"
     ))
  "Face for current instruction."
  :group 'virgil)

(defvar v/debug-state nil)
(defvar v/debug-pc nil)
(defvar v/debug-prog nil)
(defvar v/debug-source nil)
(defvar v/debug-sourceinfo nil)

(define-derived-mode v/debug-mode special-mode "Bad Apple!! debugger"
  "Major mode for displaying debugger information."
  :group 'virgil)
(defun v/get-debug-program-buffer ()
  "Return the debug program buffer."
  (unless (get-buffer v/debug-program-buffer)
    (with-current-buffer (get-buffer-create v/debug-program-buffer)
      (v/debug-mode)))
  (get-buffer v/debug-program-buffer))

(defun v/write (text &optional face)
  "Write TEXT to the current buffer and apply FACE."
  (let ((text-final (if face (propertize text 'face face) text)))
    (insert text-final)))

(defun v/write-line (line &optional face)
  "Write LINE and a newline to the current buffer and apply FACE."
  (v/write (concat line "\n") face))

(defun v/debug-render-instruction (ins cur)
  "Render INS to the current buffer.
If CUR is non-nil, this is the active instruction."
  (let ((face (if cur 'v/debug-ins-highlight 'v/debug-ins))) 
    (cond
      ((stringp ins) (v/write-line ins face))
      ((listp ins) (v/write-line (format "%s %s" (caar ins) (cdar ins)) face))
      (t (error "unknown instruction format: %s" ins)))))

(defun v/debug-render-program ()
  "Render the current program state."
  (with-current-buffer (v/get-debug-program-buffer)
    (-let ( ((&alist 'instructions) v/debug-prog)
            (inhibit-read-only t))
      (erase-buffer)
      (--each (seq-into instructions 'list)
        (v/debug-render-instruction it (= v/debug-pc it-index)))
      (when-let* ((win (get-buffer-window (v/get-debug-program-buffer))))
        (with-selected-window win
          (goto-char 0)
          (forward-line v/debug-pc))))))

(defun v/handle-message (msg)
  "Handle the message MSG."
  (-let (((&alist 'cmd 'args) msg))
    (cond
      ((s-equals? cmd "StateUpdate")
        (setf
          v/debug-pc (seq-elt args 0)
          v/debug-state (seq-elt args 1)
          v/debug-sourceinfo (seq-elt args 2))
        (v/debug-render-program))
      ((s-equals? cmd "Program")
        (setf v/debug-prog args))
      ((s-equals? cmd "Source")
        (setf v/debug-source args))
      (t (message "virgil: unknown response type %s" cmd)))))

(defun v/get-complete-line ()
  "Kill a line followed by a newline if it exists, and nil otherwise."
  (let ((l (thing-at-point 'line t)))
    (if (and l (s-contains? "\n" l))
        (progn
          (delete-region (line-beginning-position) (line-beginning-position 2))
          l)
      nil)))
(defun v/handle-lines ()
  "Call `v/handle-message' on every complete line of the current buffer."
  (let ((l (v/get-complete-line)))
    (when (and l (not (s-blank? l)))
      (v/handle-message (json-read-from-string l))
      (v/handle-lines))))
(defun v/process-filter (proc data)
  "Process filter for PROC and DATA."
  (with-current-buffer (get-buffer-create v/debug-buffer)
    (when (not (marker-position (process-mark proc)))
      (set-marker (process-mark proc) (point-max)))
    (goto-char (process-mark proc))
    (insert data)
    (set-marker (process-mark proc) (point))
    (goto-char (point-min))
    (v/handle-lines)))

(defun v/debug-encode-cmd (cmd)
  "Encode CMD to JSON."
  (let* ( (nm (cond
                ((and (symbolp cmd) cmd) cmd)
                ((and (listp cmd) (symbolp (car cmd)) (car cmd)) (car cmd))
                (t (error "Invalid command: %s" cmd))))
          (args (if (listp cmd) (cdr cmd) nil)))
    (json-encode
      (append
        `((cmd . ,(s-titleize (format "%s" nm))))
        (cond
          ((> (length args) 1) `((args . ,args)))
          ((= (length args) 1) `((args . ,(car args))))
          (t '()))))))
(defun v/debug-cmd (cmd)
  "Send CMD to the debugger process."
  (process-send-string v/debug-process (s-concat (v/debug-encode-cmd cmd) "\n")))

(defun v/debug-stop ()
  "Stop the debugger process."
  (interactive)
  (when (process-live-p (get-process v/debug-process))
    (delete-process v/debug-process)))

(defun v/debug (path)
  "Debug the C source at PATH."
  (interactive)
  (v/debug-stop)
  (setf
    v/debug-state nil
    v/debug-pc nil
    v/debug-prog nil
    v/debug-source nil
    v/debug-sourceinfo nil)
  (make-process
    :name v/debug-process
    :command (list v/path "debug" path)
    :buffer nil
    :stderr v/debug-log-buffer
    :filter #'v/process-filter
    ))

(provide 'virgil)
;;; virgil.el ends here
