#lang racket

(require racket/list
         racket/match
         "inventory.rkt"
         "syntax.rkt")

(provide (struct-out site-id)
         (struct-out elaboration-choice)
         (struct-out elaboration)
         elaborate-core)

(struct site-id (source line column ordinal kind) #:transparent)
(struct elaboration-choice (source line column kind detail) #:transparent)
(struct elaboration (ast choices sites) #:transparent)

(define (node-source node)
  (if (core-list? node) (core-list-source node) (core-atom-source node)))
(define (node-line node)
  (if (core-list? node) (core-list-line node) (core-atom-line node)))
(define (node-column node)
  (if (core-list? node) (core-list-column node) (core-atom-column node)))

(define (atom-at node value)
  (core-atom value (node-source node) (node-line node) (node-column node) #f #f))

(define (app-at node head . arguments)
  (core-list 'paren (cons (atom-at node head) arguments)
             (node-source node) (node-line node) (node-column node) #f #f))

(define (head-of node)
  (and (core-list? node)
       (eq? (core-list-shape node) 'paren)
       (pair? (core-list-elements node))
       (core-atom? (first (core-list-elements node)))
       (core-atom-value (first (core-list-elements node)))))

(define (contains-event-label? node)
  (and (core-list? node)
       (for/or ([element (in-list (core-list-elements node))])
         (and (core-atom? element)
              (eq? (core-atom-value element) ':Eventuality)))))

(define (collect-sites ast)
  (define ordinal 0)
  (define found '())
  (define (walk node)
    (when (core-list? node)
      (define head (head-of node))
      (when (member head '(Context Vague))
        (set! ordinal (add1 ordinal))
        (set! found
              (cons (site-id (node-source node) (node-line node)
                             (node-column node) ordinal head)
                    found)))
      (for ([element (in-list (core-list-elements node))]) (walk element))))
  (walk ast)
  (reverse found))

(define (elaborate-core ast [inv (load-inventory)])
  (define choices '())
  (define (record! node kind detail)
    (set! choices
          (cons (elaboration-choice (node-source node) (node-line node)
                                    (node-column node) kind detail)
                choices)))
  (define (walk node)
    (cond
      [(core-atom? node) node]
      [else
       (define elements (core-list-elements node))
       (define head (head-of node))
       (define walked (map walk elements))
       (define rebuilt (struct-copy core-list node [elements walked]))
       (cond
         [(and (eq? head 'Close) (= (length walked) 2))
          (define operand (second walked))
          (define operand-head (head-of operand))
          (define row (and operand-head (inventory-row inv operand-head)))
          (define detail
            (cond
              [(contains-event-label? operand) 'explicit-event]
              [(and row (eq? (row-decl-event-mode row) 'direct-event)) 'direct-row]
              [else 'eventless-or-derived]))
          (record! rebuilt 'Close detail)
          rebuilt]
         [(and (eq? head 'Assert) (= (length walked) 2))
          (define content (second walked))
          (if (member (head-of content) '(Close CloseClause))
              rebuilt
              (begin
                (record! rebuilt 'force-boundary-shorthand 'actual-holding-state)
                (struct-copy
                 core-list rebuilt
                 [elements
                  (list (first walked)
                        (app-at content 'CloseClause
                                (app-at content 'ActualClause
                                        (app-at content 'StateClause content))))])))]
         [else rebuilt])]))
  (define sites (collect-sites ast))
  (define result (walk ast))
  (elaboration result (reverse choices) sites))

