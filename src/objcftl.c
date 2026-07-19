/****************************************************************************
**
** TEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEST
**
*/

#include "objcftl.h"

#include "ariths.h"
#include "bool.h"
#include "error.h"
#include "gapstate.h"
#include "gvars.h"
#include "integer.h"
#include "modules.h"
#include "plist.h"


#ifdef HPCGAP
static ModuleStateOffset CFTLStateOffset = -1;

struct CFTLModuleState {
#endif
    DECL_MODULE_STATE Obj WORD_STACK;
    DECL_MODULE_STATE Obj WORD_EXPONENT_STACK;
    DECL_MODULE_STATE Obj SYLLABLE_STACK;
    DECL_MODULE_STATE Obj EXPONENT_STACK;
#ifdef HPCGAP
};

// for debugging from GDB / lldb, we mark this as extern inline
extern inline struct CFTLModuleState *CFTLState(void)
{
    return (struct CFTLModuleState *)StateSlotsAtOffset(CFTLStateOffset);
}
#define WORD_STACK          (CFTLState()->WORD_STACK)
#define WORD_EXPONENT_STACK (CFTLState()->WORD_EXPONENT_STACK)
#define SYLLABLE_STACK      (CFTLState()->SYLLABLE_STACK)
#define EXPONENT_STACK      (CFTLState()->EXPONENT_STACK)
#endif

static inline Obj IncInt(Obj x)
{
    return IS_INTOBJ(x) && x != INTOBJ_MAX ? (Obj)((Int)x + 4)
                                            : SumInt(x, INTOBJ_INT(1));
}
static inline Obj DecInt(Obj x)
{
    return IS_INTOBJ(x) && x != INTOBJ_MIN ? (Obj)((Int)x - 4)
                                            : DiffInt(x, INTOBJ_INT(1));
}
static inline Obj FastAInvInt(Obj x)
{
    return IS_INTOBJ(x) && x != INTOBJ_MIN ? INTOBJ_INT(-INT_INTOBJ(x))
                                            : AInvInt(x);
}
static inline Obj AbsIntObj(Obj x)
{
    return IS_NEG_INT(x) ? FastAInvInt(x) : x;
}

#define IS_INT_ZERO(n) ((n) == INTOBJ_INT(0))
#define GET_COMMUTE(g) INT_INTOBJ(ELM_PLIST(commute, (g)))
#define GET_EXPONENT(g) ((g) <= LEN_PLIST(exp) ? ELM_PLIST(exp, (g)) : (Obj)0)
#define GET_POWER(g) ((g) <= LEN_PLIST(pow) ? ELM_PLIST(pow, (g)) : (Obj)0)
#define GET_IPOWER(g) ((g) <= LEN_PLIST(ipow) ? ELM_PLIST(ipow, (g)) : (Obj)0)
#define GET_CONJ(h,g) ((h) <= LEN_PLIST(conj) && (g) <= LEN_PLIST(ELM_PLIST(conj,h)) ? ELM_PLIST(ELM_PLIST(conj,h),g) : (Obj)0)
#define GET_ICONJ(h,g) ((h) <= LEN_PLIST(iconj) && (g) <= LEN_PLIST(ELM_PLIST(iconj,h)) ? ELM_PLIST(ELM_PLIST(iconj,h),g) : (Obj)0)
static Obj PowerWord(Obj pcp, Obj word, Obj power, Int bottom);
#define PUSH_STACK(word, exponent) do { \
    Obj pushed_word = (word), pushed_exponent = (exponent); \
    if (LEN_PLIST(pushed_word) > 2 && !LtInt(pushed_exponent, POWER_THRESHOLD)) { \
        pushed_word = PowerWord(pcp, pushed_word, pushed_exponent, st); \
        pushed_exponent = INTOBJ_INT(1); \
    } \
    if (LEN_PLIST(pushed_word) == 0 || IS_INT_ZERO(pushed_exponent)) break; \
    st++; GROW_PLIST(wst, st); GROW_PLIST(west, st); \
    GROW_PLIST(sst, st); GROW_PLIST(est, st); \
    SET_ELM_PLIST(wst, st, pushed_word); SET_ELM_PLIST(west, st, pushed_exponent); \
    SET_ELM_PLIST(sst, st, INTOBJ_INT(1)); \
    SET_ELM_PLIST(est, st, ELM_PLIST(pushed_word, 2)); \
    CHANGED_BAG(wst); CHANGED_BAG(west); CHANGED_BAG(est); \
} while (0)

#define POWER_THRESHOLD INTOBJ_INT(5)
/* This component is owned by the polycyclic package, not GAP's historic
   objcftl.h interface.  UpdatePolycyclicCollector clears it with the other
   derived collector data. */
#define PC_POWER_AUTOMORPHISMS 31

static void AddIn(Obj list, Obj w, Obj e)
{
    Int g, i;
    Obj r, s, t;
    for (i = 1; i < LEN_PLIST(w); i += 2) {
        g = INT_INTOBJ(ELM_PLIST(w, i));
        s = ELM_PLIST(w, i + 1);
        C_PROD_FIA(t, s, e);
        r = ELM_PLIST(list, g);
        C_SUM_FIA(s, t, r);
        SET_ELM_PLIST(list, g, s); CHANGED_BAG(list);
    }
}

static Obj CollectPolycycFrom(Obj pcp, Obj list, Obj word, Int bottom);

static Obj NewExponentVector(Int ngens)
{
    Int i;
    Obj v = NEW_PLIST(T_PLIST, ngens);
    SET_LEN_PLIST(v, ngens);
    for (i = 1; i <= ngens; i++)
        SET_ELM_PLIST(v, i, INTOBJ_INT(0));
    CHANGED_BAG(v);
    return v;
}

static void SetListElement(Obj list, Int pos, Obj value)
{
    if (LEN_PLIST(list) < pos) {
        GROW_PLIST(list, pos);
        SET_LEN_PLIST(list, pos);
    }
    SET_ELM_PLIST(list, pos, value); CHANGED_BAG(list);
}

static Obj WordFromVector(Obj vector, Int ngens)
{
    Int g, len = 0;
    Obj word = NEW_PLIST(T_PLIST, 2 * ngens);
    for (g = 1; g <= ngens; g++) {
        Obj e = ELM_PLIST(vector, g);
        if (!IS_INT_ZERO(e)) {
            SET_ELM_PLIST(word, ++len, INTOBJ_INT(g));
            SET_ELM_PLIST(word, ++len, e);
        }
    }
    SET_LEN_PLIST(word, len); CHANGED_BAG(word);
    return word;
}

static Obj InverseWord(Obj word)
{
    Int i, len = LEN_PLIST(word);
    Obj inverse = NEW_PLIST(T_PLIST, len);
    SET_LEN_PLIST(inverse, len);
    for (i = 1; i <= len; i += 2) {
        SET_ELM_PLIST(inverse, len - i, ELM_PLIST(word, i));
        SET_ELM_PLIST(inverse, len - i + 1, FastAInvInt(ELM_PLIST(word, i + 1)));
    }
    CHANGED_BAG(inverse);
    return inverse;
}

/* Return word^power in normal form.  Nested collection starts above bottom,
   so the caller's pending collection frames remain intact. */
static Obj PowerWord(Obj pcp, Obj word, Obj power, Int bottom)
{
    Int ngens = INT_INTOBJ(CONST_ADDR_OBJ(pcp)[PC_NUMBER_OF_GENERATORS]);
    Obj base, result, square, normal;

    if (IS_INT_ZERO(power))
        return NEW_PLIST(T_PLIST, 0);
    if (IS_NEG_INT(power)) {
        normal = NewExponentVector(ngens);
        CollectPolycycFrom(pcp, normal, InverseWord(word), bottom);
        return PowerWord(pcp, WordFromVector(normal, ngens), FastAInvInt(power), bottom);
    }

    base = NewExponentVector(ngens);
    CollectPolycycFrom(pcp, base, word, bottom);
    result = NewExponentVector(ngens);
    while (!IS_INT_ZERO(power)) {
        if (!IS_INT_ZERO(ModInt(power, INTOBJ_INT(2))))
            CollectPolycycFrom(pcp, result, WordFromVector(base, ngens), bottom);
        power = QuoInt(power, INTOBJ_INT(2));
        if (!IS_INT_ZERO(power)) {
            square = NewExponentVector(ngens);
            normal = WordFromVector(base, ngens);
            CollectPolycycFrom(pcp, square, normal, bottom);
            CollectPolycycFrom(pcp, square, normal, bottom);
            base = square;
        }
    }
    return WordFromVector(result, ngens);
}

/* Evaluate the automorphism described by images[1..ngens] on word. */
static Obj EvaluateAutomorphism(Obj pcp, Obj images, Obj word, Int bottom)
{
    Int ngens = INT_INTOBJ(CONST_ADDR_OBJ(pcp)[PC_NUMBER_OF_GENERATORS]);
    Int i, g;
    Obj result = NewExponentVector(ngens);
    for (i = 1; i < LEN_PLIST(word); i += 2) {
        g = INT_INTOBJ(ELM_PLIST(word, i));
        CollectPolycycFrom(pcp, result,
                            PowerWord(pcp, ELM_PLIST(images, g),
                                      ELM_PLIST(word, i + 1), bottom), bottom);
    }
    return WordFromVector(result, ngens);
}

/* images is the action of g by conjugation.  Binary composition computes
   the action of g^power without applying that action power times. */
static Obj PowerAutomorphism(Obj pcp, Int g, Obj power, Int bottom)
{
    Int ngens = INT_INTOBJ(CONST_ADDR_OBJ(pcp)[PC_NUMBER_OF_GENERATORS]);
    Obj gens = CONST_ADDR_OBJ(pcp)[PC_GENERATORS];
    Obj conj;
    Obj cache = CONST_ADDR_OBJ(pcp)[PC_POWER_AUTOMORPHISMS];
    Obj entry, maps, result = NEW_PLIST(T_PLIST, ngens);
    Int h, sign, bit = 1;

    if (IS_NEG_INT(power)) {
        power = FastAInvInt(power);
        conj = CONST_ADDR_OBJ(pcp)[PC_CONJUGATESINVERSE];
        sign = 2;
    }
    else {
        conj = CONST_ADDR_OBJ(pcp)[PC_CONJUGATES];
        sign = 1;
    }
    entry = LEN_PLIST(cache) >= g ? ELM_PLIST(cache, g) : (Obj)0;
    if (!entry) {
        entry = NEW_PLIST(T_PLIST, 2); SET_LEN_PLIST(entry, 2);
        SET_ELM_PLIST(entry, 1, NEW_PLIST(T_PLIST, 0));
        SET_ELM_PLIST(entry, 2, NEW_PLIST(T_PLIST, 0)); CHANGED_BAG(entry);
        SetListElement(cache, g, entry);
    }
    maps = ELM_PLIST(entry, sign);
    if (LEN_PLIST(maps) == 0) {
        Obj first = NEW_PLIST(T_PLIST, ngens);
        SET_LEN_PLIST(first, ngens);
        for (h = 1; h <= ngens; h++) {
            Obj image = GET_CONJ(h, g);
            SET_ELM_PLIST(first, h, image ? image : ELM_PLIST(gens, h));
        }
        CHANGED_BAG(first); SetListElement(maps, 1, first);
    }

    /* Materialise and retain only the powers of two that are needed. */
    {
        Obj remaining = power;
        while (!IS_INT_ZERO(QuoInt(remaining, INTOBJ_INT(2)))) {
            Obj previous, composed;
            remaining = QuoInt(remaining, INTOBJ_INT(2)); bit++;
            if (LEN_PLIST(maps) >= bit && ELM_PLIST(maps, bit)) continue;
            previous = ELM_PLIST(maps, bit - 1);
            composed = NEW_PLIST(T_PLIST, ngens); SET_LEN_PLIST(composed, ngens);
            for (h = 1; h <= ngens; h++)
                SET_ELM_PLIST(composed, h,
                    EvaluateAutomorphism(pcp, previous, ELM_PLIST(previous, h), bottom));
            CHANGED_BAG(composed); SetListElement(maps, bit, composed);
        }
    }

    SET_LEN_PLIST(result, ngens);
    for (h = 1; h <= ngens; h++)
        SET_ELM_PLIST(result, h, ELM_PLIST(gens, h));
    CHANGED_BAG(result);
    bit = 1;
    while (!IS_INT_ZERO(power)) {
        if (!IS_INT_ZERO(ModInt(power, INTOBJ_INT(2)))) {
            Obj composed = NEW_PLIST(T_PLIST, ngens);
            SET_LEN_PLIST(composed, ngens);
            for (h = 1; h <= ngens; h++)
                SET_ELM_PLIST(composed, h,
                              EvaluateAutomorphism(pcp, ELM_PLIST(maps, bit),
                                                    ELM_PLIST(result, h), bottom));
            CHANGED_BAG(composed); result = composed;
        }
        power = QuoInt(power, INTOBJ_INT(2));
        bit++;
    }
    return result;
}

static Obj CollectPolycycFrom(Obj pcp, Obj list, Obj word, Int bottom)
{
    Int ngens = INT_INTOBJ(CONST_ADDR_OBJ(pcp)[PC_NUMBER_OF_GENERATORS]);
    Obj commute = CONST_ADDR_OBJ(pcp)[PC_COMMUTE];
    Obj gens = CONST_ADDR_OBJ(pcp)[PC_GENERATORS];
    Obj igens = CONST_ADDR_OBJ(pcp)[PC_INVERSES];
    Obj pow = CONST_ADDR_OBJ(pcp)[PC_POWERS];
    Obj ipow = CONST_ADDR_OBJ(pcp)[PC_INVERSEPOWERS];
    Obj exp = CONST_ADDR_OBJ(pcp)[PC_EXPONENTS];
    Obj wst = WORD_STACK, west = WORD_EXPONENT_STACK;
    Obj sst = SYLLABLE_STACK, est = EXPONENT_STACK;
    Obj conj = 0, iconj = 0;
    Int st = bottom, g, syl, h, hh;
    Obj e, ee, ge, mge, we, s, t, w, x = 0, y = 0;

    if (LEN_PLIST(word) == 0) return (Obj)0;
    if (LEN_PLIST(list) < ngens) ErrorQuit("vector too short", 0, 0);
    if (LEN_PLIST(word) % 2) ErrorQuit("Length of word odd", 0, 0);
    PUSH_STACK(word, INTOBJ_INT(1));

    while (st > bottom) {
        w = ELM_PLIST(wst, st); syl = INT_INTOBJ(ELM_PLIST(sst, st));
        g = INT_INTOBJ(ELM_PLIST(w, syl));

        /* A large single generator, including a syllable inside a longer
           word, is moved past the suffix by a binary-powered conjugation. */
        C_PROD_FIA(e, ELM_PLIST(west, st), ELM_PLIST(est, st));
        if ((ELM_PLIST(west, st) == INTOBJ_INT(1) ||
             (syl == 1 && LEN_PLIST(w) == 2)) &&
            !LtInt(AbsIntObj(e), POWER_THRESHOLD) &&
            g != GET_COMMUTE(g)) {
            Obj images, suffix;
            C_PROD_FIA(e, ELM_PLIST(west, st), ELM_PLIST(est, st));
            images = PowerAutomorphism(pcp, g, e, st);
            suffix = NEW_PLIST(T_PLIST, ngens); SET_LEN_PLIST(suffix, ngens);
            for (h = g + 1; h <= ngens; h++) {
                Obj he = ELM_PLIST(list, h);
                if (IS_INT_ZERO(he)) SET_ELM_PLIST(suffix, h, (Obj)0);
                else {
                    SET_ELM_PLIST(list, h, INTOBJ_INT(0)); CHANGED_BAG(list);
                    SET_ELM_PLIST(suffix, h,
                        PowerWord(pcp, ELM_PLIST(images, h), he, st));
                }
            }
            CHANGED_BAG(suffix);
            C_SUM_FIA(ge, ELM_PLIST(list, g), e);
            SET_ELM_PLIST(list, g, ge); CHANGED_BAG(list);
            y = (Obj)0;
            if ((e = GET_EXPONENT(g))) {
                if (!LtInt(ge, e)) {
                    mge = ModInt(ge, e); SET_ELM_PLIST(list, g, mge); CHANGED_BAG(list);
                    if ((y = GET_POWER(g))) ge = QuoInt(ge, e);
                }
                else if (IS_NEG_INT(ge)) {
                    mge = ModInt(ge, e); SET_ELM_PLIST(list, g, mge); CHANGED_BAG(list);
                    if ((y = GET_IPOWER(g))) {
                        ge = QuoInt(ge, e);
                        if (!IS_INT_ZERO(mge)) ge = DecInt(ge);
                        ge = AInvInt(ge);
                    }
                }
            }
            for (h = ngens; h > g; h--)
                if (ELM_PLIST(suffix, h)) PUSH_STACK(ELM_PLIST(suffix, h), INTOBJ_INT(1));
            if (y) PUSH_STACK(y, ge);
            if (ELM_PLIST(west, st) == INTOBJ_INT(1))
                SET_ELM_PLIST(est, st, INTOBJ_INT(0));
            else
                st--;
            goto advance_stack;
        }

        if (st > bottom + 1 && syl == 1 && g == GET_COMMUTE(g)) {
            e = ELM_PLIST(west, st); AddIn(list, w, e);
            for (h = g; h <= ngens; h++) {
                s = ELM_PLIST(list, h); if (IS_INT_ZERO(s)) continue; y = 0;
                if ((e = GET_EXPONENT(h))) {
                    if (!LtInt(s, e)) { t = ModInt(s, e); SET_ELM_PLIST(list,h,t); CHANGED_BAG(list); if ((y=GET_POWER(h))) e=QuoInt(s,e); }
                    else if (IS_NEG_INT(s)) { t=ModInt(s,e); SET_ELM_PLIST(list,h,t); CHANGED_BAG(list); if ((y=GET_IPOWER(h))) { e=QuoInt(s,e); if (!IS_INT_ZERO(t)) e=DecInt(e); e=AInvInt(e); } }
                }
                if (y) AddIn(list, y, e);
            }
            st--;
        }
        else {
            if (g == GET_COMMUTE(g)) {
                s = ELM_PLIST(list,g); t = ELM_PLIST(est,st);
                C_SUM_FIA(ge,s,t); SET_ELM_PLIST(est,st,INTOBJ_INT(0));
            }
            else {
                e = ELM_PLIST(est,st);
                if (IS_POS_INT(e)) { e=DecInt(e); SET_ELM_PLIST(est,st,e); CHANGED_BAG(est); conj=CONST_ADDR_OBJ(pcp)[PC_CONJUGATES]; iconj=CONST_ADDR_OBJ(pcp)[PC_INVERSECONJUGATES]; ge=IncInt(ELM_PLIST(list,g)); }
                else { C_SUM_FIA(ee,e,INTOBJ_INT(1)); e=ee; SET_ELM_PLIST(est,st,e); CHANGED_BAG(est); conj=CONST_ADDR_OBJ(pcp)[PC_CONJUGATESINVERSE]; iconj=CONST_ADDR_OBJ(pcp)[PC_INVERSECONJUGATESINVERSE]; ge=DecInt(ELM_PLIST(list,g)); }
            }
            SET_ELM_PLIST(list,g,ge); CHANGED_BAG(list); y=0;
            if ((e=GET_EXPONENT(g))) {
                if (!LtInt(ge,e)) { mge=ModInt(ge,e); SET_ELM_PLIST(list,g,mge); CHANGED_BAG(list); if ((y=GET_POWER(g))) ge=QuoInt(ge,e); }
                else if (IS_NEG_INT(ge)) { mge=ModInt(ge,e); SET_ELM_PLIST(list,g,mge); CHANGED_BAG(list); if ((y=GET_IPOWER(g))) { ge=QuoInt(ge,e); if (!IS_INT_ZERO(mge)) ge=DecInt(ge); ge=AInvInt(ge); } }
            }
            hh=h=GET_COMMUTE(g);
            for (;h>g;h--) { e=ELM_PLIST(list,h); if (!IS_INT_ZERO(e) && (IS_POS_INT(e) ? GET_CONJ(h,g) : GET_ICONJ(h,g))) break; }
            if (h>g || y) for (;hh>h;hh--) { e=ELM_PLIST(list,hh); if (!IS_INT_ZERO(e)) { SET_ELM_PLIST(list,hh,INTOBJ_INT(0)); x=IS_POS_INT(e)?ELM_PLIST(gens,hh):ELM_PLIST(igens,hh); if (IS_NEG_INT(e)) e=FastAInvInt(e); PUSH_STACK(x,e); } }
            for (;h>g;h--) { e=ELM_PLIST(list,h); if (!IS_INT_ZERO(e)) { SET_ELM_PLIST(list,h,INTOBJ_INT(0)); x=IS_POS_INT(e)?GET_CONJ(h,g):GET_ICONJ(h,g); if (!x) x=IS_POS_INT(e)?ELM_PLIST(gens,h):ELM_PLIST(igens,h); if (IS_NEG_INT(e)) e=FastAInvInt(e); PUSH_STACK(x,e); } }
            if (y) PUSH_STACK(y,ge);
        }

advance_stack:
        while (st > bottom && IS_INT_ZERO(ELM_PLIST(est,st))) {
            w=ELM_PLIST(wst,st); syl=INT_INTOBJ(ELM_PLIST(sst,st))+2;
            if (syl > LEN_PLIST(w)) { we=DecInt(ELM_PLIST(west,st)); if (IS_INT_ZERO(we)) st--; else { SET_ELM_PLIST(west,st,we); SET_ELM_PLIST(sst,st,INTOBJ_INT(1)); SET_ELM_PLIST(est,st,ELM_PLIST(w,2)); CHANGED_BAG(west); CHANGED_BAG(est); } }
            else { SET_ELM_PLIST(sst,st,INTOBJ_INT(syl)); SET_ELM_PLIST(est,st,ELM_PLIST(w,syl+1)); CHANGED_BAG(est); }
        }
    }
    return (Obj)0;
}

static Obj CollectPolycyc(Obj pcp, Obj list, Obj word)
{
    return CollectPolycycFrom(pcp, list, word, 0);
}
static Obj FuncCollectPolycyclic(Obj self, Obj pcp, Obj list, Obj word)
{
    CollectPolycyc(pcp, list, word); return (Obj)0;
}

static StructGVarFunc GVarFuncs[] = {
    GVAR_FUNC_3ARGS(CollectPolycyclic, pcp, list, word), {0,0,0,0,0}
};
static Int InitKernel(StructInitInfo *module)
{
    InitHdlrFuncsFromTable(GVarFuncs); return 0;
}
static Int InitLibrary(StructInitInfo *module)
{
    ExportAsConstantGVar(PC_NUMBER_OF_GENERATORS); ExportAsConstantGVar(PC_GENERATORS);
    ExportAsConstantGVar(PC_INVERSES); ExportAsConstantGVar(PC_COMMUTE);
    ExportAsConstantGVar(PC_POWERS); ExportAsConstantGVar(PC_INVERSEPOWERS);
    ExportAsConstantGVar(PC_EXPONENTS); ExportAsConstantGVar(PC_CONJUGATES);
    ExportAsConstantGVar(PC_INVERSECONJUGATES); ExportAsConstantGVar(PC_CONJUGATESINVERSE);
    ExportAsConstantGVar(PC_INVERSECONJUGATESINVERSE); ExportAsConstantGVar(PC_DEEP_THOUGHT_POLS);
    ExportAsConstantGVar(PC_DEEP_THOUGHT_BOUND); ExportAsConstantGVar(PC_ORDERS);
    ExportAsConstantGVar(PC_DEFAULT_TYPE); InitGVarFuncsFromTable(GVarFuncs); return 0;
}
static Int InitModuleState(void)
{
    InitGlobalBag(&WORD_STACK,"WORD_STACK"); InitGlobalBag(&WORD_EXPONENT_STACK,"WORD_EXPONENT_STACK");
    InitGlobalBag(&SYLLABLE_STACK,"SYLLABLE_STACK"); InitGlobalBag(&EXPONENT_STACK,"EXPONENT_STACK");
    WORD_STACK=NEW_PLIST(T_PLIST,4096); WORD_EXPONENT_STACK=NEW_PLIST(T_PLIST,4096);
    SYLLABLE_STACK=NEW_PLIST(T_PLIST,4096); EXPONENT_STACK=NEW_PLIST(T_PLIST,4096); return 0;
}
static StructInitInfo module = {
    .type=MODULE_BUILTIN, .name="objcftl", .initKernel=InitKernel, .initLibrary=InitLibrary,
#ifdef HPCGAP
    .moduleStateSize=sizeof(struct CFTLModuleState), .moduleStateOffsetPtr=&CFTLStateOffset,
#endif
    .initModuleState=InitModuleState,
};
StructInitInfo *InitInfoPcc(void) { return &module; }
