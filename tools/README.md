These tools include a helper module which parses Lambda2Gmu code using regular
names and translates it to use de Bruijn indices.

Another tool is able to parse the annotated variant of Lambda2Gmu and apply the
encoding algorithm to the term. A few examples are shown below.

## Head

Original code in annotated Lambda2Gmu:
```
Λa. Λn. λv: ((a,(n) Succ) Vector).
  matchgadt v as Vector returning a with {
    Nil[a2](unused) => <>
  | Cons[a2, n2](da) => fst(da)
  }
```

Translated into pDOT:

```
λ(a: {GenT: ⊥..⊤}) λ(n: {GenT: ⊥..⊤})
λ(v: ((env.Vector ∧ {A1 == a.GenT}) ∧ {A2 == (env.Succ ∧ {A1 == n.GenT})})) 
   let _tl_0 = (ν(_4: {GenT == a.GenT}){ GenT =v a.GenT }) in 
   let _v_1 = (v) in 
   let _case_2 = 
      (λ(_arg_5: (env.Nil ∧ _v_1.type)) 
         let unused = (_arg_5.data) in
         let _res_6 = (lib.unit) in _res_6) 
   in 
   let _case_3 = 
      (λ(_arg_7: (env.Cons ∧ _v_1.type)) 
         let da = (_arg_7.data) in 
         let _res_8 = (let _v_9 = (da) in _v_9.fst) in _res_8) 
   in 
   let _partialApp_10 = (_v_1.pmatch _tl_0) in let _partialApp_11 = (_partialApp_10 _case_2) in _partialApp_11 _case_3
```

## Zip

Original code in annotated Lambda2Gmu:
```
fix $self: (∀a. ∀b. ∀n. ((a,n) Vector -> (b,n) Vector -> (a * b,n) Vector)).
  Λa. Λb. Λn. λva: ((a,n) Vector). λvb: ((b,n) Vector).
  matchgadt va as Vector returning (a * b,n) Vector with {
     Nil[a2](unused) => Nil[a * b](<>)
   | Cons[a2, n2](da) =>
     matchgadt vb as Vector returning (a * b,n) Vector with {
       Nil[b2](unused) => <>
     | Cons[b2, n3](db) =>
         let h = <fst(da) : a2, fst(db) : b2> in
           let t = (((($self[a])[b])[n2]) (snd(da))) (snd(db)) in
             Cons[(a*b),n2](<h : a*b, t : (a*b, n2) Vector>)
           end
         end
     }
  }
```

Translated into pDOT:
```
let _hlp_0 = (ν(self: {
    fix: ∀(_2: lib.Unit) ∀(a: {GenT: ⊥..⊤}) ∀(b: {GenT: ⊥..⊤}) ∀(n: {GenT: ⊥..⊤}) 
         ∀(_3: ((env.Vector ∧ {A1 == a.GenT}) ∧ {A2 == n.GenT})) 
         ∀(_4: ((env.Vector ∧ {A1 == b.GenT}) ∧ {A2 == n.GenT})) 
            ((env.Vector ∧ {A1 == (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}))}) ∧ {A2 == n.GenT})}){
    fix =v 
         λ(_2: lib.Unit) λ(a: {GenT: ⊥..⊤}) λ(b: {GenT: ⊥..⊤}) λ(n: {GenT: ⊥..⊤}) 
         λ(va: ((env.Vector ∧ {A1 == a.GenT}) ∧ {A2 == n.GenT})) 
         λ(vb: ((env.Vector ∧ {A1 == b.GenT}) ∧ {A2 == n.GenT})) 
            let _tl_5 = (ν(_9: {
               GenT == ((env.Vector ∧ {A1 == (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}))}) ∧ {A2 == n.GenT})}){ 
               GenT =v ((env.Vector ∧ {A1 == (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}))}) ∧ {A2 == n.GenT}) 
            }) in
            let _v_6 = (va) in
            let _case_7 = 
               (λ(_arg_10: (env.Nil ∧ _v_6.type)) 
                  let unused = (_arg_10.data) in 
                  let _res_11 = 
                     (let _ts_12 = (ν(_14: {
                         B1 == (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}))}){ 
                         B1 =v (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT})) }) in 
                      let _v_13 = (lib.unit) in let _partialApp_15 = (env.nil _ts_12) in _partialApp_15 _v_13) 
                  in _res_11) 
            in 
            let _case_8 = 
                (λ(_arg_16: (env.Cons ∧ _v_6.type)) 
                   let da = (_arg_16.data) in 
                   let _res_17 = 
                      (let _tl_18 = (ν(_22: {
                          GenT == ((env.Vector ∧ {A1 == (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}))}) ∧ {A2 == n.GenT})}){
                          GenT =v ((env.Vector ∧ {A1 == (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}))}) ∧ {A2 == n.GenT}) }) in 
                       let _v_19 = (vb) in
                       let _case_20 = 
                          (λ(_arg_23: (env.Nil ∧ _v_19.type)) 
                             let unused = (_arg_23.data) in 
                             let _res_24 = (lib.unit) in _res_24)
                       in
                       let _case_21 = 
                          (λ(_arg_25: (env.Cons ∧ _v_19.type)) 
                             let db = (_arg_25.data) in 
                             let _res_26 = 
                                (let h = 
                                   (let _v1_27 = (let _v_31 = (da) in _v_31.fst) in 
                                    let _v2_28 = (let _v_32 = (db) in _v_32.fst) in 
                                    let _tl_29 = (ν(_30: ({T1 == _arg_16.B1} ∧ {T2 == _arg_25.B1})){ 
                                                           T1 =v _arg_16.B1;    T2 =v _arg_25.B1 }) in 
                                    let _partialApp_33 = (lib.tuple _tl_29) in let _partialApp_34 = (_partialApp_33 _v1_27) in _partialApp_34 _v2_28)
                                 in 
                                 let t = 
                                    (let _v1_35 = (let _v1_37 = 
                                           (let _v_39 = (let _v_42 = (let _v_45 = (_self_1.fix lib.unit) in 
                                            let _tl_46 = (ν(_47: {GenT == a.GenT}){ GenT =v a.GenT }) in _v_45 _tl_46) in 
                                            let _tl_43 = (ν(_44: {GenT == b.GenT}){ GenT =v b.GenT }) in _v_42 _tl_43) in 
                                            let _tl_40 = (ν(_41: {GenT == _arg_16.B2}){ GenT =v _arg_16.B2 }) in _v_39 _tl_40) in
                                            let _v2_38 = (let _v_48 = (da) in _v_48.snd) in _v1_37 _v2_38) in 
                                            let _v2_36 = (let _v_49 = (db) in _v_49.snd) in _v1_35 _v2_36) in 
                                 let _ts_50 = (ν(_52: ({B1 == (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}))} ∧ {B2 == _arg_16.B2})){ 
                                                        B1 =v (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}));    B2 =v _arg_16.B2 }) in 
                                 let _v_51 = 
                                     (let _v1_53 = (h) in 
                                      let _v2_54 = (t) in 
                                      let _tl_55 = (ν(_56: ({T1 == (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}))} ∧ {T2 == ((env.Vector ∧ {A1 == (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}))}) ∧ {A2 == _arg_16.B2})})){ 
                                                             T1 =v (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}));    T2 =v ((env.Vector ∧ {A1 == (lib.Tuple ∧ ({T1 == a.GenT} ∧ {T2 == b.GenT}))}) ∧ {A2 == _arg_16.B2}) }) in 
                                      let _partialApp_57 = (lib.tuple _tl_55) in let _partialApp_58 = (_partialApp_57 _v1_53) in _partialApp_58 _v2_54) in let _partialApp_59 = (env.cons _ts_50) in _partialApp_59 _v_51)
                             in _res_26)
                       in let _partialApp_60 = (_v_19.pmatch _tl_18) in let _partialApp_61 = (_partialApp_60 _case_20) in _partialApp_61 _case_21) 
                   in _res_17)
            in
            let _partialApp_62 = (_v_6.pmatch _tl_5) in let _partialApp_63 = (_partialApp_62 _case_7) in _partialApp_63 _case_8 
}) in _hlp_0.fix lib.unit
```
