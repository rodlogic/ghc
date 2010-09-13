
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
\section{Tidying up Core}

\begin{code}
module TidyPgm( mkBootModDetailsDs, mkBootModDetailsTc, 
       		tidyProgram, globaliseAndTidyId ) where

#include "HsVersions.h"

import TcRnTypes
import FamInstEnv
import DynFlags
import CoreSyn
import CoreUnfold
import CoreFVs
import CoreTidy
import CoreMonad
import CoreUtils
import Rules
import CoreArity	( exprArity, exprBotStrictness_maybe )
import Class		( classAllSelIds )
import VarEnv
import VarSet
import Var
import Id
import IdInfo
import InstEnv
import Demand
import BasicTypes
import Name hiding (varName)
import NameSet
import IfaceEnv
import NameEnv
import TcType
import DataCon
import TyCon
import Module
import HscTypes
import Maybes
import UniqSupply
import Outputable
import FastBool hiding ( fastOr )
import Util
import FastString

import Data.List	( sortBy )
import Data.IORef	( IORef, readIORef, writeIORef )
\end{code}


Constructing the TypeEnv, Instances, Rules, VectInfo from which the
ModIface is constructed, and which goes on to subsequent modules in
--make mode.

Most of the interface file is obtained simply by serialising the
TypeEnv.  One important consequence is that if the *interface file*
has pragma info if and only if the final TypeEnv does. This is not so
important for *this* module, but it's essential for ghc --make:
subsequent compilations must not see (e.g.) the arity if the interface
file does not contain arity If they do, they'll exploit the arity;
then the arity might change, but the iface file doesn't change =>
recompilation does not happen => disaster. 

For data types, the final TypeEnv will have a TyThing for the TyCon,
plus one for each DataCon; the interface file will contain just one
data type declaration, but it is de-serialised back into a collection
of TyThings.

%************************************************************************
%*				 					*
		Plan A: simpleTidyPgm
%*				 					* 
%************************************************************************


Plan A: mkBootModDetails: omit pragmas, make interfaces small
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
* Ignore the bindings

* Drop all WiredIn things from the TypeEnv 
	(we never want them in interface files)

* Retain all TyCons and Classes in the TypeEnv, to avoid
	having to find which ones are mentioned in the
	types of exported Ids

* Trim off the constructors of non-exported TyCons, both
	from the TyCon and from the TypeEnv

* Drop non-exported Ids from the TypeEnv

* Tidy the types of the DFunIds of Instances, 
  make them into GlobalIds, (they already have External Names)
  and add them to the TypeEnv

* Tidy the types of the (exported) Ids in the TypeEnv,
  make them into GlobalIds (they already have External Names)

* Drop rules altogether

* Tidy the bindings, to ensure that the Caf and Arity
  information is correct for each top-level binder; the 
  code generator needs it. And to ensure that local names have
  distinct OccNames in case of object-file splitting

\begin{code}
-- This is Plan A: make a small type env when typechecking only,
-- or when compiling a hs-boot file, or simply when not using -O
--
-- We don't look at the bindings at all -- there aren't any
-- for hs-boot files

mkBootModDetailsTc :: HscEnv -> TcGblEnv -> IO ModDetails
mkBootModDetailsTc hsc_env 
        TcGblEnv{ tcg_exports   = exports,
                  tcg_type_env  = type_env,
                  tcg_insts     = insts,
                  tcg_fam_insts = fam_insts
                }
  = mkBootModDetails hsc_env exports type_env insts fam_insts

mkBootModDetailsDs :: HscEnv -> ModGuts -> IO ModDetails
mkBootModDetailsDs hsc_env 
        ModGuts{ mg_exports   = exports,
                 mg_types     = type_env,
                 mg_insts     = insts,
                 mg_fam_insts = fam_insts
                }
  = mkBootModDetails hsc_env exports type_env insts fam_insts
  
mkBootModDetails :: HscEnv -> [AvailInfo] -> NameEnv TyThing
                 -> [Instance] -> [FamInstEnv.FamInst] -> IO ModDetails
mkBootModDetails hsc_env exports type_env insts fam_insts
  = do	{ let dflags = hsc_dflags hsc_env 
	; showPass dflags CoreTidy

	; let { insts'     = tidyInstances globaliseAndTidyId insts
	      ; dfun_ids   = map instanceDFunId insts'
	      ; type_env1  = tidyBootTypeEnv (availsToNameSet exports) type_env
	      ; type_env'  = extendTypeEnvWithIds type_env1 dfun_ids
	      }
	; return (ModDetails { md_types     = type_env'
			     , md_insts     = insts'
			     , md_fam_insts = fam_insts
			     , md_rules     = []
			     , md_anns      = []
			     , md_exports   = exports
                             , md_vect_info = noVectInfo
                             })
	}
  where

tidyBootTypeEnv :: NameSet -> TypeEnv -> TypeEnv
tidyBootTypeEnv exports type_env 
  = tidyTypeEnv True False exports type_env final_ids
  where
	-- Find the LocalIds in the type env that are exported
	-- Make them into GlobalIds, and tidy their types
	--
	-- It's very important to remove the non-exported ones
	-- because we don't tidy the OccNames, and if we don't remove
	-- the non-exported ones we'll get many things with the
	-- same name in the interface file, giving chaos.
    final_ids = [ globaliseAndTidyId id
		| id <- typeEnvIds type_env
		, isLocalId id
		, keep_it id ]

        -- default methods have their export flag set, but everything
        -- else doesn't (yet), because this is pre-desugaring, so we
        -- must test both.
    keep_it id = isExportedId id || idName id `elemNameSet` exports



globaliseAndTidyId :: Id -> Id
-- Takes an LocalId with an External Name, 
-- makes it into a GlobalId 
--     * unchanged Name (might be Internal or External)
--     * unchanged details
--     * VanillaIdInfo (makes a conservative assumption about Caf-hood)
globaliseAndTidyId id	
  = Id.setIdType (globaliseId id) tidy_type
  where
    tidy_type = tidyTopType (idType id)
\end{code}


%************************************************************************
%*				 					*
	Plan B: tidy bindings, make TypeEnv full of IdInfo
%*				 					* 
%************************************************************************

Plan B: include pragmas, make interfaces 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
* Figure out which Ids are externally visible

* Tidy the bindings, externalising appropriate Ids

* Drop all Ids from the TypeEnv, and add all the External Ids from 
  the bindings.  (This adds their IdInfo to the TypeEnv; and adds
  floated-out Ids that weren't even in the TypeEnv before.)

Step 1: Figure out external Ids
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Note [choosing external names]

See also the section "Interface stability" in the
RecompilationAvoidance commentary:
  http://hackage.haskell.org/trac/ghc/wiki/Commentary/Compiler/RecompilationAvoidance

First we figure out which Ids are "external" Ids.  An
"external" Id is one that is visible from outside the compilation
unit.  These are
	a) the user exported ones
	b) ones mentioned in the unfoldings, workers, 
	   or rules of externally-visible ones 

While figuring out which Ids are external, we pick a "tidy" OccName
for each one.  That is, we make its OccName distinct from the other
external OccNames in this module, so that in interface files and
object code we can refer to it unambiguously by its OccName.  The
OccName for each binder is prefixed by the name of the exported Id
that references it; e.g. if "f" references "x" in its unfolding, then
"x" is renamed to "f_x".  This helps distinguish the different "x"s
from each other, and means that if "f" is later removed, things that
depend on the other "x"s will not need to be recompiled.  Of course,
if there are multiple "f_x"s, then we have to disambiguate somehow; we
use "f_x0", "f_x1" etc.

As far as possible we should assign names in a deterministic fashion.
Each time this module is compiled with the same options, we should end
up with the same set of external names with the same types.  That is,
the ABI hash in the interface should not change.  This turns out to be
quite tricky, since the order of the bindings going into the tidy
phase is already non-deterministic, as it is based on the ordering of
Uniques, which are assigned unpredictably.

To name things in a stable way, we do a depth-first-search of the
bindings, starting from the exports sorted by name.  This way, as long
as the bindings themselves are deterministic (they sometimes aren't!),
the order in which they are presented to the tidying phase does not
affect the names we assign.

Step 2: Tidy the program
~~~~~~~~~~~~~~~~~~~~~~~~
Next we traverse the bindings top to bottom.  For each *top-level*
binder

 1. Make it into a GlobalId; its IdDetails becomes VanillaGlobal, 
    reflecting the fact that from now on we regard it as a global, 
    not local, Id

 2. Give it a system-wide Unique.
    [Even non-exported things need system-wide Uniques because the
    byte-code generator builds a single Name->BCO symbol table.]

    We use the NameCache kept in the HscEnv as the
    source of such system-wide uniques.

    For external Ids, use the original-name cache in the NameCache
    to ensure that the unique assigned is the same as the Id had 
    in any previous compilation run.

 3. Rename top-level Ids according to the names we chose in step 1.
    If it's an external Id, make it have a External Name, otherwise
    make it have an Internal Name.  This is used by the code generator
    to decide whether to make the label externally visible

 4. Give it its UTTERLY FINAL IdInfo; in ptic, 
  	* its unfolding, if it should have one
	
	* its arity, computed from the number of visible lambdas

	* its CAF info, computed from what is free in its RHS

		
Finally, substitute these new top-level binders consistently
throughout, including in unfoldings.  We also tidy binders in
RHSs, so that they print nicely in interfaces.

\begin{code}
tidyProgram :: HscEnv -> ModGuts -> IO (CgGuts, ModDetails)
tidyProgram hsc_env  (ModGuts { mg_module = mod, mg_exports = exports, 
				mg_types = type_env, 
				mg_insts = insts, mg_fam_insts = fam_insts,
				mg_binds = binds, 
				mg_rules = imp_rules,
                                mg_vect_info = vect_info,
				mg_dir_imps = dir_imps, 
				mg_anns = anns,
                                mg_deps = deps, 
				mg_foreign = foreign_stubs,
			        mg_hpc_info = hpc_info,
                                mg_modBreaks = modBreaks })

  = do	{ let { dflags     = hsc_dflags hsc_env
	      ; omit_prags = dopt Opt_OmitInterfacePragmas dflags
	      ; expose_all = dopt Opt_ExposeAllUnfoldings  dflags
	      ; th	   = dopt Opt_TemplateHaskell      dflags
              }
	; showPass dflags CoreTidy

    	; let { implicit_binds = getImplicitBinds type_env }

        ; (unfold_env, tidy_occ_env)
              <- chooseExternalIds hsc_env mod omit_prags expose_all 
                                   binds implicit_binds imp_rules

        ; let { ext_rules = findExternalRules omit_prags binds imp_rules unfold_env }
	        -- Glom together imp_rules and rules currently attached to binders
		-- Then pick just the ones we need to expose
		-- See Note [Which rules to expose]

	; let { (tidy_env, tidy_binds)
                 = tidyTopBinds hsc_env unfold_env tidy_occ_env binds }

	; let { export_set = availsToNameSet exports
	      ; final_ids  = [ id | id <- bindersOfBinds tidy_binds, 
				    isExternalName (idName id)]
              ; tidy_type_env = tidyTypeEnv omit_prags th export_set
					    type_env final_ids
	      ; tidy_insts    = tidyInstances (lookup_dfun tidy_type_env) insts
		-- A DFunId will have a binding in tidy_binds, and so
		-- will now be in final_env, replete with IdInfo
		-- Its name will be unchanged since it was born, but
		-- we want Global, IdInfo-rich (or not) DFunId in the
		-- tidy_insts

	      ; tidy_rules = tidyRules tidy_env ext_rules
		-- You might worry that the tidy_env contains IdInfo-rich stuff
		-- and indeed it does, but if omit_prags is on, ext_rules is
		-- empty

              ; tidy_vect_info = tidyVectInfo tidy_env vect_info

	      -- See Note [Injecting implicit bindings]
    	      ; all_tidy_binds = implicit_binds ++ tidy_binds

	      ; alg_tycons = filter isAlgTyCon (typeEnvTyCons type_env)
	      }

   	; endPass dflags CoreTidy all_tidy_binds tidy_rules

	  -- If the endPass didn't print the rules, but ddump-rules is on, print now
	; dumpIfSet (dopt Opt_D_dump_rules dflags 
                     && (not (dopt Opt_D_dump_simpl dflags))) 
		    CoreTidy
                    (ptext (sLit "rules"))
                    (pprRulesForUser tidy_rules)

        ; let dir_imp_mods = moduleEnvKeys dir_imps

	; return (CgGuts { cg_module   = mod, 
			   cg_tycons   = alg_tycons,
			   cg_binds    = all_tidy_binds,
			   cg_dir_imps = dir_imp_mods,
			   cg_foreign  = foreign_stubs,
			   cg_dep_pkgs = dep_pkgs deps,
			   cg_hpc_info = hpc_info,
                           cg_modBreaks = modBreaks }, 

		   ModDetails { md_types     = tidy_type_env,
				md_rules     = tidy_rules,
				md_insts     = tidy_insts,
                                md_vect_info = tidy_vect_info,
                                md_fam_insts = fam_insts,
				md_exports   = exports,
				md_anns      = anns      -- are already tidy
                              })
	}

lookup_dfun :: TypeEnv -> Var -> Id
lookup_dfun type_env dfun_id
  = case lookupTypeEnv type_env (idName dfun_id) of
	Just (AnId dfun_id') -> dfun_id'
	_other -> pprPanic "lookup_dfun" (ppr dfun_id)

--------------------------
tidyTypeEnv :: Bool 	-- Compiling without -O, so omit prags
	    -> Bool	-- Template Haskell is on
	    -> NameSet -> TypeEnv -> [Id] -> TypeEnv

-- The competed type environment is gotten from
--	Dropping any wired-in things, and then
-- 	a) keeping the types and classes
--	b) removing all Ids, 
--	c) adding Ids with correct IdInfo, including unfoldings,
--		gotten from the bindings
-- From (c) we keep only those Ids with External names;
--	    the CoreTidy pass makes sure these are all and only
--	    the externally-accessible ones
-- This truncates the type environment to include only the 
-- exported Ids and things needed from them, which saves space

tidyTypeEnv omit_prags th exports type_env final_ids
 = let  type_env1 = filterNameEnv keep_it type_env
	type_env2 = extendTypeEnvWithIds type_env1 final_ids
	type_env3 | omit_prags = mapNameEnv (trimThing th exports) type_env2
		  | otherwise  = type_env2
    in 
    type_env3
  where
   	-- We keep GlobalIds, because they won't appear 
	-- in the bindings from which final_ids are derived!
	-- (The bindings bind LocalIds.)
    keep_it thing | isWiredInThing thing = False
    keep_it (AnId id) = isGlobalId id	-- Keep GlobalIds (e.g. class ops)
    keep_it _other    = True		-- Keep all TyCons, DataCons, and Classes

--------------------------
isWiredInThing :: TyThing -> Bool
isWiredInThing thing = isWiredInName (getName thing)

--------------------------
trimThing :: Bool -> NameSet -> TyThing -> TyThing
-- Trim off inessentials, for boot files and no -O
trimThing th exports (ATyCon tc)
   | not th && not (mustExposeTyCon exports tc)
   = ATyCon (makeTyConAbstract tc)	-- Note [Trimming and Template Haskell]

trimThing _th _exports (AnId id)
   | not (isImplicitId id) 
   = AnId (id `setIdInfo` vanillaIdInfo)

trimThing _th _exports other_thing 
  = other_thing


{- Note [Trimming and Template Haskell]
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Consider (Trac #2386) this
	module M(T, makeOne) where
	  data T = Yay String
	  makeOne = [| Yay "Yep" |]
Notice that T is exported abstractly, but makeOne effectively exports it too!
A module that splices in $(makeOne) will then look for a declartion of Yay,
so it'd better be there.  Hence, brutally but simply, we switch off type
constructor trimming if TH is enabled in this module. -}


mustExposeTyCon :: NameSet	-- Exports
		-> TyCon	-- The tycon
		-> Bool 	-- Can its rep be hidden?
-- We are compiling without -O, and thus trying to write as little as 
-- possible into the interface file.  But we must expose the details of
-- any data types whose constructors or fields are exported
mustExposeTyCon exports tc
  | not (isAlgTyCon tc) 	-- Synonyms
  = True
  | isEnumerationTyCon tc	-- For an enumeration, exposing the constructors
  = True			-- won't lead to the need for further exposure
				-- (This includes data types with no constructors.)
  | isFamilyTyCon tc		-- Open type family
  = True

  | otherwise			-- Newtype, datatype
  = any exported_con (tyConDataCons tc)
	-- Expose rep if any datacon or field is exported

  || (isNewTyCon tc && isFFITy (snd (newTyConRhs tc)))
	-- Expose the rep for newtypes if the rep is an FFI type.  
	-- For a very annoying reason.  'Foreign import' is meant to
	-- be able to look through newtypes transparently, but it
	-- can only do that if it can "see" the newtype representation
  where
    exported_con con = any (`elemNameSet` exports) 
			   (dataConName con : dataConFieldLabels con)

tidyInstances :: (DFunId -> DFunId) -> [Instance] -> [Instance]
tidyInstances tidy_dfun ispecs
  = map tidy ispecs
  where
    tidy ispec = setInstanceDFunId ispec $
		 tidy_dfun (instanceDFunId ispec)
\end{code}

\begin{code}
tidyVectInfo :: TidyEnv -> VectInfo -> VectInfo
tidyVectInfo (_, var_env) info@(VectInfo { vectInfoVar     = vars
                                         , vectInfoPADFun  = pas
                                         , vectInfoIso     = isos })
  = info { vectInfoVar    = tidy_vars
         , vectInfoPADFun = tidy_pas
         , vectInfoIso    = tidy_isos }
  where
    tidy_vars = mkVarEnv
              $ map tidy_var_mapping
              $ varEnvElts vars

    tidy_pas = mapNameEnv tidy_snd_var pas
    tidy_isos = mapNameEnv tidy_snd_var isos

    tidy_var_mapping (from, to) = (from', (from', lookup_var to))
      where from' = lookup_var from
    tidy_snd_var (x, var) = (x, lookup_var var)
      
    lookup_var var = lookupWithDefaultVarEnv var_env var var
\end{code}


%************************************************************************
%*									*
	Implicit bindings
%*									*
%************************************************************************

Note [Injecting implicit bindings]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We inject the implict bindings right at the end, in CoreTidy.
Some of these bindings, notably record selectors, are not
constructed in an optimised form.  E.g. record selector for
	data T = MkT { x :: {-# UNPACK #-} !Int }
Then the unfolding looks like
	x = \t. case t of MkT x1 -> let x = I# x1 in x
This generates bad code unless it's first simplified a bit.  That is
why CoreUnfold.mkImplicitUnfolding uses simleExprOpt to do a bit of
optimisation first.  (Only matters when the selector is used curried;
eg map x ys.)  See Trac #2070.

[Oct 09: in fact, record selectors are no longer implicit Ids at all,
because we really do want to optimise them properly. They are treated
much like any other Id.  But doing "light" optimisation on an implicit
Id still makes sense.]

At one time I tried injecting the implicit bindings *early*, at the
beginning of SimplCore.  But that gave rise to real difficulty,
becuase GlobalIds are supposed to have *fixed* IdInfo, but the
simplifier and other core-to-core passes mess with IdInfo all the
time.  The straw that broke the camels back was when a class selector
got the wrong arity -- ie the simplifier gave it arity 2, whereas
importing modules were expecting it to have arity 1 (Trac #2844).
It's much safer just to inject them right at the end, after tidying.

Oh: two other reasons for injecting them late:

  - If implicit Ids are already in the bindings when we start TidyPgm,
    we'd have to be careful not to treat them as external Ids (in
    the sense of findExternalIds); else the Ids mentioned in *their*
    RHSs will be treated as external and you get an interface file 
    saying      a18 = <blah>
    but nothing refererring to a18 (because the implicit Id is the 
    one that does, and implicit Ids don't appear in interface files).

  - More seriously, the tidied type-envt will include the implicit
    Id replete with a18 in its unfolding; but we won't take account
    of a18 when computing a fingerprint for the class; result chaos.
    
There is one sort of implicit binding that is injected still later,
namely those for data constructor workers. Reason (I think): it's
really just a code generation trick.... binding itself makes no sense.
See CorePrep Note [Data constructor workers].

\begin{code}
getImplicitBinds :: TypeEnv -> [CoreBind]
getImplicitBinds type_env
  = map get_defn (concatMap implicit_ids (typeEnvElts type_env))
  where
    implicit_ids (ATyCon tc)  = mapCatMaybes dataConWrapId_maybe (tyConDataCons tc)
    implicit_ids (AClass cls) = classAllSelIds cls
    implicit_ids _            = []
    
    get_defn :: Id -> CoreBind
    get_defn id = NonRec id (unfoldingTemplate (realIdUnfolding id))
\end{code}


%************************************************************************
%*				 					*
\subsection{Step 1: finding externals}
%*				 					* 
%************************************************************************

Sete Note [choosing external names].

\begin{code}
type UnfoldEnv  = IdEnv (Name{-new name-}, Bool {-show unfolding-})
  -- Maps each top-level Id to its new Name (the Id is tidied in step 2)
  -- The Unique is unchanged.  If the new Name is external, it will be
  -- visible in the interface file.  
  --
  -- Bool => expose unfolding or not.

chooseExternalIds :: HscEnv
                  -> Module
                  -> Bool -> Bool
		  -> [CoreBind]
                  -> [CoreBind]
		  -> [CoreRule]
                  -> IO (UnfoldEnv, TidyOccEnv)
	-- Step 1 from the notes above

chooseExternalIds hsc_env mod omit_prags expose_all binds implicit_binds imp_id_rules
  = do { (unfold_env1,occ_env1) <- search init_work_list emptyVarEnv init_occ_env
       ; let internal_ids = filter (not . (`elemVarEnv` unfold_env1)) binders
       ; tidy_internal internal_ids unfold_env1 occ_env1 }
 where
  nc_var = hsc_NC hsc_env 

  -- init_ext_ids is the intial list of Ids that should be
  -- externalised.  It serves as the starting point for finding a
  -- deterministic, tidy, renaming for all external Ids in this
  -- module.
  -- 
  -- It is sorted, so that it has adeterministic order (i.e. it's the
  -- same list every time this module is compiled), in contrast to the
  -- bindings, which are ordered non-deterministically.
  init_work_list = zip init_ext_ids init_ext_ids
  init_ext_ids   = sortBy (compare `on` getOccName) $
                   filter is_external binders

  -- An Id should be external if either (a) it is exported or
  -- (b) it appears in the RHS of a local rule for an imported Id.   
  -- See Note [Which rules to expose]
  is_external id = isExportedId id || id `elemVarSet` rule_rhs_vars
  rule_rhs_vars = foldr (unionVarSet . ruleRhsFreeVars) emptyVarSet imp_id_rules

  binders          = bindersOfBinds binds
  implicit_binders = bindersOfBinds implicit_binds
  binder_set       = mkVarSet binders

  avoids   = [getOccName name | bndr <- binders ++ implicit_binders,
                                let name = idName bndr,
                                isExternalName name ]
		-- In computing our "avoids" list, we must include
		--	all implicit Ids
		--	all things with global names (assigned once and for
		--					all by the renamer)
		-- since their names are "taken".
		-- The type environment is a convenient source of such things.
                -- In particular, the set of binders doesn't include
                -- implicit Ids at this stage.

	-- We also make sure to avoid any exported binders.  Consider
	--	f{-u1-} = 1	-- Local decl
	--	...
	--	f{-u2-} = 2	-- Exported decl
	--
	-- The second exported decl must 'get' the name 'f', so we
	-- have to put 'f' in the avoids list before we get to the first
	-- decl.  tidyTopId then does a no-op on exported binders.
  init_occ_env = initTidyOccEnv avoids


  search :: [(Id,Id)]    -- The work-list: (external id, referrring id)
  	    		 -- Make a tidy, external Name for the external id,
                         --   add it to the UnfoldEnv, and do the same for the
                         --   transitive closure of Ids it refers to
  	    		 -- The referring id is used to generate a tidy
			 ---  name for the external id
         -> UnfoldEnv    -- id -> (new Name, show_unfold)
         -> TidyOccEnv   -- occ env for choosing new Names
         -> IO (UnfoldEnv, TidyOccEnv)

  search [] unfold_env occ_env = return (unfold_env, occ_env)

  search ((idocc,referrer) : rest) unfold_env occ_env
    | idocc `elemVarEnv` unfold_env = search rest unfold_env occ_env
    | otherwise = do
      (occ_env', name') <- tidyTopName mod nc_var (Just referrer) occ_env idocc
      let 
          (new_ids, show_unfold)
                | omit_prags = ([], False)
                | otherwise  = addExternal expose_all refined_id

		-- 'idocc' is an *occurrence*, but we need to see the
		-- unfolding in the *definition*; so look up in binder_set
          refined_id = case lookupVarSet binder_set idocc of
                         Just id -> id
                         Nothing -> WARN( True, ppr idocc ) idocc

          unfold_env' = extendVarEnv unfold_env idocc (name',show_unfold)
          referrer' | isExportedId refined_id = refined_id
                    | otherwise               = referrer
      --
      search (zip new_ids (repeat referrer') ++ rest) unfold_env' occ_env'

  tidy_internal :: [Id] -> UnfoldEnv -> TidyOccEnv
                -> IO (UnfoldEnv, TidyOccEnv)
  tidy_internal []       unfold_env occ_env = return (unfold_env,occ_env)
  tidy_internal (id:ids) unfold_env occ_env = do
      (occ_env', name') <- tidyTopName mod nc_var Nothing occ_env id
      let unfold_env' = extendVarEnv unfold_env id (name',False)
      tidy_internal ids unfold_env' occ_env'

addExternal :: Bool -> Id -> ([Id],Bool)
addExternal expose_all id = (new_needed_ids, show_unfold)
  where
    new_needed_ids = unfold_ids ++
                     filter (\id -> isLocalId id &&
                                    not (id `elemVarSet` unfold_set))
                       (varSetElems spec_ids) -- XXX non-det ordering

    idinfo	   = idInfo id
    never_active   = isNeverActive (inlinePragmaActivation (inlinePragInfo idinfo))
    loop_breaker   = isNonRuleLoopBreaker (occInfo idinfo)
    bottoming_fn   = isBottomingSig (strictnessInfo idinfo `orElse` topSig)
    spec_ids	   = specInfoFreeVars (specInfo idinfo)

	-- Stuff to do with the Id's unfolding
	-- We leave the unfolding there even if there is a worker
	-- In GHCI the unfolding is used by importers
    show_unfold = isJust mb_unfold_ids
    (unfold_set, unfold_ids) = mb_unfold_ids `orElse` (emptyVarSet, [])

    mb_unfold_ids :: Maybe (IdSet, [Id])	-- Nothing => don't unfold
    mb_unfold_ids = case unfoldingInfo idinfo of
		      CoreUnfolding { uf_tmpl = unf_rhs, uf_src = src, uf_guidance = guide } 
					    | show_unfolding src guide
					    -> Just (unf_ext_ids src unf_rhs)
		      DFunUnfolding _ _ ops -> Just (exprsFvsInOrder ops)
		      _                     -> Nothing
                  where
                    unf_ext_ids (InlineWrapper v) _ = (unitVarSet v, [v])
                    unf_ext_ids _           unf_rhs = exprFvsInOrder unf_rhs
		    -- For a wrapper, externalise the wrapper id rather than the
		    -- fvs of the rhs.  The two usually come down to the same thing
		    -- but I've seen cases where we had a wrapper id $w but a
		    -- rhs where $w had been inlined; see Trac #3922

    show_unfolding unf_source unf_guidance
       =  expose_all 	     -- 'expose_all' says to expose all 
			     -- unfoldings willy-nilly

       || isInlineRuleSource unf_source	     -- Always expose things whose 
       	  		     		     -- source is an inline rule

       || not (bottoming_fn	 -- No need to inline bottom functions
	   || never_active	 -- Or ones that say not to
	   || loop_breaker	 -- Or that are loop breakers
	   || neverUnfoldGuidance unf_guidance)

-- We want a deterministic free-variable list.  exprFreeVars gives us
-- a VarSet, which is in a non-deterministic order when converted to a
-- list.  Hence, here we define a free-variable finder that returns
-- the free variables in the order that they are encountered.
--
-- Note [choosing external names]

exprFvsInOrder :: CoreExpr -> (VarSet, [Id])
exprFvsInOrder e = run (dffvExpr e)

exprsFvsInOrder :: [CoreExpr] -> (VarSet, [Id])
exprsFvsInOrder es = run (mapM_ dffvExpr es)

run :: DFFV () -> (VarSet, [Id])
run (DFFV m) = case m emptyVarSet [] of
                 (set,ids,_) -> (set,ids)

newtype DFFV a = DFFV (VarSet -> [Var] -> (VarSet,[Var],a))

instance Monad DFFV where
  return a = DFFV $ \set ids -> (set, ids, a)
  (DFFV m) >>= k = DFFV $ \set ids ->
    case m set ids of
       (set',ids',a) -> case k a of
                          DFFV f -> f set' ids' 

insert :: Var -> DFFV ()
insert v = DFFV $ \ set ids  -> case () of 
 _ | v `elemVarSet` set -> (set,ids,())
   | otherwise          -> (extendVarSet set v, v:ids, ())

dffvExpr :: CoreExpr -> DFFV ()
dffvExpr e = go emptyVarSet e
  where
    go scope e = case e of
      Var v | isLocalId v && not (v `elemVarSet` scope) -> insert v
      App e1 e2          -> do go scope e1; go scope e2
      Lam v e            -> go (extendVarSet scope v) e
      Note _ e           -> go scope e
      Cast e _           -> go scope e
      Let (NonRec x r) e -> do go scope r; go (extendVarSet scope x) e
      Let (Rec prs) e    -> do let scope' = extendVarSetList scope (map fst prs)
                               mapM_ (go scope') (map snd prs)
                               go scope' e
      Case e b _ as      -> do go scope e
                               mapM_ (go_alt (extendVarSet scope b)) as
      _other             -> return ()

    go_alt scope (_,xs,r) = go (extendVarSetList scope xs) r
\end{code}


--------------------------------------------------------------------
--		tidyTopName
-- This is where we set names to local/global based on whether they really are 
-- externally visible (see comment at the top of this module).  If the name
-- was previously local, we have to give it a unique occurrence name if
-- we intend to externalise it.

\begin{code}
tidyTopName :: Module -> IORef NameCache -> Maybe Id -> TidyOccEnv
	    -> Id -> IO (TidyOccEnv, Name)
tidyTopName mod nc_var maybe_ref occ_env id
  | global && internal = return (occ_env, localiseName name)

  | global && external = return (occ_env, name)
	-- Global names are assumed to have been allocated by the renamer,
	-- so they already have the "right" unique
	-- And it's a system-wide unique too

  -- Now we get to the real reason that all this is in the IO Monad:
  -- we have to update the name cache in a nice atomic fashion

  | local  && internal = do { nc <- readIORef nc_var
			    ; let (nc', new_local_name) = mk_new_local nc
			    ; writeIORef nc_var nc'
			    ; return (occ_env', new_local_name) }
	-- Even local, internal names must get a unique occurrence, because
	-- if we do -split-objs we externalise the name later, in the code generator
	--
	-- Similarly, we must make sure it has a system-wide Unique, because
	-- the byte-code generator builds a system-wide Name->BCO symbol table

  | local  && external = do { nc <- readIORef nc_var
			    ; let (nc', new_external_name) = mk_new_external nc
			    ; writeIORef nc_var nc'
			    ; return (occ_env', new_external_name) }

  | otherwise = panic "tidyTopName"
  where
    name	= idName id
    external    = isJust maybe_ref
    global	= isExternalName name
    local	= not global
    internal	= not external
    loc		= nameSrcSpan name

    old_occ     = nameOccName name
    new_occ
      | Just ref <- maybe_ref, ref /= id = 
          mkOccName (occNameSpace old_occ) $
             let
                 ref_str = occNameString (getOccName ref)
                 occ_str = occNameString old_occ
             in
             case occ_str of
               '$':'w':_ -> occ_str
                  -- workers: the worker for a function already
                  -- includes the occname for its parent, so there's
                  -- no need to prepend the referrer.
               _other | isSystemName name -> ref_str
                      | otherwise         -> ref_str ++ '_' : occ_str
                  -- If this name was system-generated, then don't bother
                  -- to retain its OccName, just use the referrer.  These
                  -- system-generated names will become "f1", "f2", etc. for
                  -- a referrer "f".
      | otherwise = old_occ

    (occ_env', occ') = tidyOccName occ_env new_occ

    mk_new_local nc = (nc { nsUniqs = us2 }, mkInternalName uniq occ' loc)
 		    where
		      (us1, us2) = splitUniqSupply (nsUniqs nc)
		      uniq	 = uniqFromSupply us1

    mk_new_external nc = allocateGlobalBinder nc mod occ' loc
	-- If we want to externalise a currently-local name, check
	-- whether we have already assigned a unique for it.
	-- If so, use it; if not, extend the table.
	-- All this is done by allcoateGlobalBinder.
	-- This is needed when *re*-compiling a module in GHCi; we must
	-- use the same name for externally-visible things as we did before.
\end{code}

\begin{code}
findExternalRules :: Bool	-- Omit pragmas
                  -> [CoreBind]
		  -> [CoreRule]	-- Local rules for imported fns
	          -> UnfoldEnv	-- Ids that are exported, so we need their rules
	          -> [CoreRule]
  -- The complete rules are gotten by combining
  --	a) local rules for imported Ids
  --	b) rules embedded in the top-level Ids
findExternalRules omit_prags binds imp_id_rules unfold_env
  | omit_prags = []
  | otherwise  = filterOut internal_rule (imp_id_rules ++ local_rules)
  where
    local_rules  = [ rule
 		   | id <- bindersOfBinds binds,
                     external_id id,
		     rule <- idCoreRules id
		   ]

    internal_rule rule
	=  any (not . external_id) (varSetElems (ruleLhsFreeIds rule))
		-- Don't export a rule whose LHS mentions a locally-defined
		--  Id that is completely internal (i.e. not visible to an
		-- importing module)

    external_id id
      | Just (name,_) <- lookupVarEnv unfold_env id = isExternalName name
      | otherwise = False
\end{code}

Note [Which rules to expose]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
findExternalRules filters imp_rules to avoid binders that 
aren't externally visible; but the externally-visible binders 
are computed (by findExternalIds) assuming that all orphan
rules are externalised (see init_ext_ids in function 
'search'). So in fact we may export more than we need. 
(It's a sort of mutual recursion.)

%************************************************************************
%*									*
\subsection{Step 2: top-level tidying}
%*									*
%************************************************************************


\begin{code}
-- TopTidyEnv: when tidying we need to know
--   * nc_var: The NameCache, containing a unique supply and any pre-ordained Names.  
--	  These may have arisen because the
--	  renamer read in an interface file mentioning M.$wf, say,
--	  and assigned it unique r77.  If, on this compilation, we've
--	  invented an Id whose name is $wf (but with a different unique)
--	  we want to rename it to have unique r77, so that we can do easy
--	  comparisons with stuff from the interface file
--
--   * occ_env: The TidyOccEnv, which tells us which local occurrences 
--     are 'used'
--
--   * subst_env: A Var->Var mapping that substitutes the new Var for the old

tidyTopBinds :: HscEnv
	     -> UnfoldEnv
             -> TidyOccEnv
	     -> [CoreBind]
	     -> (TidyEnv, [CoreBind])

tidyTopBinds hsc_env unfold_env init_occ_env binds
  = tidy init_env binds
  where
    init_env = (init_occ_env, emptyVarEnv)

    this_pkg = thisPackage (hsc_dflags hsc_env)

    tidy env []     = (env, [])
    tidy env (b:bs) = let (env1, b')  = tidyTopBind this_pkg unfold_env env b
			  (env2, bs') = tidy env1 bs
                      in
			  (env2, b':bs')

------------------------
tidyTopBind  :: PackageId
             -> UnfoldEnv
	     -> TidyEnv
             -> CoreBind
	     -> (TidyEnv, CoreBind)

tidyTopBind this_pkg unfold_env (occ_env,subst1) (NonRec bndr rhs)
  = (tidy_env2,  NonRec bndr' rhs')
  where
    Just (name',show_unfold) = lookupVarEnv unfold_env bndr
    caf_info      = hasCafRefs this_pkg subst1 (idArity bndr) rhs
    (bndr', rhs') = tidyTopPair show_unfold tidy_env2 caf_info name' (bndr, rhs)
    subst2        = extendVarEnv subst1 bndr bndr'
    tidy_env2     = (occ_env, subst2)

tidyTopBind this_pkg unfold_env (occ_env,subst1) (Rec prs)
  = (tidy_env2, Rec prs')
  where
    prs' = [ tidyTopPair show_unfold tidy_env2 caf_info name' (id,rhs)
           | (id,rhs) <- prs,
             let (name',show_unfold) = 
                    expectJust "tidyTopBind" $ lookupVarEnv unfold_env id
           ]

    subst2    = extendVarEnvList subst1 (bndrs `zip` map fst prs')
    tidy_env2 = (occ_env, subst2)

    bndrs = map fst prs

	-- the CafInfo for a recursive group says whether *any* rhs in
	-- the group may refer indirectly to a CAF (because then, they all do).
    caf_info 
	| or [ mayHaveCafRefs (hasCafRefs this_pkg subst1 (idArity bndr) rhs)
	     | (bndr,rhs) <- prs ] = MayHaveCafRefs
	| otherwise 		   = NoCafRefs

-----------------------------------------------------------
tidyTopPair :: Bool  -- show unfolding
	    -> TidyEnv 	-- The TidyEnv is used to tidy the IdInfo
			-- It is knot-tied: don't look at it!
	    -> CafInfo
	    -> Name		-- New name
	    -> (Id, CoreExpr) 	-- Binder and RHS before tidying
	    -> (Id, CoreExpr)
	-- This function is the heart of Step 2
	-- The rec_tidy_env is the one to use for the IdInfo
	-- It's necessary because when we are dealing with a recursive
	-- group, a variable late in the group might be mentioned
	-- in the IdInfo of one early in the group

tidyTopPair show_unfold rhs_tidy_env caf_info name' (bndr, rhs)
  = (bndr1, rhs1)
  where
    bndr1    = mkGlobalId details name' ty' idinfo'
    details  = idDetails bndr	-- Preserve the IdDetails
    ty'	     = tidyTopType (idType bndr)
    rhs1     = tidyExpr rhs_tidy_env rhs
    idinfo'  = tidyTopIdInfo rhs_tidy_env name' rhs rhs1 (idInfo bndr) 
                             show_unfold caf_info

-- tidyTopIdInfo creates the final IdInfo for top-level
-- binders.  There are two delicate pieces:
--
--  * Arity.  After CoreTidy, this arity must not change any more.
--	Indeed, CorePrep must eta expand where necessary to make
--	the manifest arity equal to the claimed arity.
--
--  * CAF info.  This must also remain valid through to code generation.
-- 	We add the info here so that it propagates to all
-- 	occurrences of the binders in RHSs, and hence to occurrences in
-- 	unfoldings, which are inside Ids imported by GHCi. Ditto RULES.
--	CoreToStg makes use of this when constructing SRTs.
tidyTopIdInfo :: TidyEnv -> Name -> CoreExpr -> CoreExpr 
              -> IdInfo -> Bool -> CafInfo -> IdInfo
tidyTopIdInfo rhs_tidy_env name orig_rhs tidy_rhs idinfo show_unfold caf_info
  | not is_external	-- For internal Ids (not externally visible)
  = vanillaIdInfo	-- we only need enough info for code generation
			-- Arity and strictness info are enough;
			--	c.f. CoreTidy.tidyLetBndr
	`setCafInfo` 	    caf_info
	`setArityInfo`	    arity
	`setStrictnessInfo` final_sig

  | otherwise		-- Externally-visible Ids get the whole lot
  = vanillaIdInfo
	`setCafInfo` 	       caf_info
	`setArityInfo`	       arity
	`setStrictnessInfo`    final_sig
        `setOccInfo`           robust_occ_info
	`setInlinePragInfo`    (inlinePragInfo idinfo)
	`setUnfoldingInfo`     unfold_info
		-- NB: we throw away the Rules
		-- They have already been extracted by findExternalRules
  where
    is_external = isExternalName name

    --------- OccInfo ------------
    robust_occ_info = zapFragileOcc (occInfo idinfo)
    -- It's important to keep loop-breaker information
    -- when we are doing -fexpose-all-unfoldings

    --------- Strictness ------------
    final_sig | Just sig <- strictnessInfo idinfo
              = WARN( _bottom_hidden sig, ppr name ) Just sig
              | Just (_, sig) <- mb_bot_str = Just sig
              | otherwise                   = Nothing

    -- If the cheap-and-cheerful bottom analyser can see that
    -- the RHS is bottom, it should jolly well be exposed
    _bottom_hidden id_sig = case mb_bot_str of
                               Nothing         -> False
                               Just (arity, _) -> not (appIsBottom id_sig arity)

    mb_bot_str = exprBotStrictness_maybe orig_rhs

    --------- Unfolding ------------
    unf_info = unfoldingInfo idinfo
    unfold_info | show_unfold = tidyUnfolding rhs_tidy_env tidy_rhs final_sig unf_info
		| otherwise   = noUnfolding
    -- NB: do *not* expose the worker if show_unfold is off,
    --     because that means this thing is a loop breaker or
    --     marked NOINLINE or something like that
    -- This is important: if you expose the worker for a loop-breaker
    -- then you can make the simplifier go into an infinite loop, because
    -- in effect the unfolding is exposed.  See Trac #1709
    -- 
    -- You might think that if show_unfold is False, then the thing should
    -- not be w/w'd in the first place.  But a legitimate reason is this:
    -- 	  the function returns bottom
    -- In this case, show_unfold will be false (we don't expose unfoldings
    -- for bottoming functions), but we might still have a worker/wrapper
    -- split (see Note [Worker-wrapper for bottoming functions] in WorkWrap.lhs

    --------- Arity ------------
    -- Usually the Id will have an accurate arity on it, because
    -- the simplifier has just run, but not always. 
    -- One case I found was when the last thing the simplifier
    -- did was to let-bind a non-atomic argument and then float
    -- it to the top level. So it seems more robust just to
    -- fix it here.
    arity = exprArity orig_rhs



------------ Unfolding  --------------
tidyUnfolding :: TidyEnv -> CoreExpr -> Maybe StrictSig -> Unfolding -> Unfolding
tidyUnfolding tidy_env _ _ (DFunUnfolding ar con ids)
  = DFunUnfolding ar con (map (tidyExpr tidy_env) ids)
tidyUnfolding tidy_env tidy_rhs strict_sig
              unf@(CoreUnfolding { uf_tmpl = unf_rhs, uf_src = src })
  | isInlineRuleSource src
  = unf { uf_tmpl = tidyExpr tidy_env unf_rhs, 	   -- Preserves OccInfo
	  uf_src  = tidyInl tidy_env src }
  | otherwise
  = mkTopUnfolding is_bot tidy_rhs
  where
    is_bot = case strict_sig of 
                Just sig -> isBottomingSig sig
                Nothing  -> False

tidyUnfolding _ _ _ unf = unf

tidyInl :: TidyEnv -> UnfoldingSource -> UnfoldingSource
tidyInl tidy_env (InlineWrapper w) = InlineWrapper (tidyVarOcc tidy_env w)
tidyInl _        inl_info          = inl_info
\end{code}

%************************************************************************
%*									*
\subsection{Figuring out CafInfo for an expression}
%*									*
%************************************************************************

hasCafRefs decides whether a top-level closure can point into the dynamic heap.
We mark such things as `MayHaveCafRefs' because this information is
used to decide whether a particular closure needs to be referenced
in an SRT or not.

There are two reasons for setting MayHaveCafRefs:
	a) The RHS is a CAF: a top-level updatable thunk.
	b) The RHS refers to something that MayHaveCafRefs

Possible improvement: In an effort to keep the number of CAFs (and 
hence the size of the SRTs) down, we could also look at the expression and 
decide whether it requires a small bounded amount of heap, so we can ignore 
it as a CAF.  In these cases however, we would need to use an additional
CAF list to keep track of non-collectable CAFs.  

\begin{code}
hasCafRefs  :: PackageId -> VarEnv Var -> Arity -> CoreExpr -> CafInfo
hasCafRefs this_pkg p arity expr 
  | is_caf || mentions_cafs 
                            = MayHaveCafRefs
  | otherwise 		    = NoCafRefs
 where
  mentions_cafs = isFastTrue (cafRefs p expr)
  is_caf = not (arity > 0 || rhsIsStatic this_pkg expr)

  -- NB. we pass in the arity of the expression, which is expected
  -- to be calculated by exprArity.  This is because exprArity
  -- knows how much eta expansion is going to be done by 
  -- CorePrep later on, and we don't want to duplicate that
  -- knowledge in rhsIsStatic below.

cafRefs :: VarEnv Id -> Expr a -> FastBool
cafRefs p (Var id)
	-- imported Ids first:
  | not (isLocalId id) = fastBool (mayHaveCafRefs (idCafInfo id))
	-- now Ids local to this module:
  | otherwise =
     case lookupVarEnv p id of
	Just id' -> fastBool (mayHaveCafRefs (idCafInfo id'))
	Nothing  -> fastBool False

cafRefs _ (Lit _) 	       = fastBool False
cafRefs p (App f a) 	       = fastOr (cafRefs p f) (cafRefs p) a
cafRefs p (Lam _ e) 	       = cafRefs p e
cafRefs p (Let b e) 	       = fastOr (cafRefss p (rhssOfBind b)) (cafRefs p) e
cafRefs p (Case e _bndr _ alts) = fastOr (cafRefs p e) (cafRefss p) (rhssOfAlts alts)
cafRefs p (Note _n e) 	       = cafRefs p e
cafRefs p (Cast e _co)         = cafRefs p e
cafRefs _ (Type _) 	       = fastBool False

cafRefss :: VarEnv Id -> [Expr a] -> FastBool
cafRefss _ [] 	  = fastBool False
cafRefss p (e:es) = fastOr (cafRefs p e) (cafRefss p) es

fastOr :: FastBool -> (a -> FastBool) -> a -> FastBool
-- hack for lazy-or over FastBool.
fastOr a f x = fastBool (isFastTrue a || isFastTrue (f x))
\end{code}
