/**CFile****************************************************************

  FileName    [.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName []

  Synopsis    []

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: .c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/cmd/cmd.h"
#include "proof/fraig/fraig.h"
#include "opt/sim/sim.h"
#include "aig/aig/aig.h"
#include "aig/saig/saig.h"
#include "aig/gia/gia.h"
#include "proof/ssw/ssw.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////

/**Function*************************************************************

  Synopsis    []

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/

/**Function*************************************************************

  Synopsis    [Verifies combinational equivalence by brute-force SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkCecSat1( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int nInsLimit )
{
    extern Abc_Ntk_t * Abc_NtkMulti( Abc_Ntk_t * pNtk, int nThresh, int nFaninMax, int fCnf, int fMulti, int fSimple, int fFactor );
    Abc_Ntk_t * pMiter;
    Abc_Ntk_t * pCnf;
    int RetValue;

    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 1, 0, 0, 0 );
    if ( pMiter == NULL )
    {
        printf( "Miter computation has failed.\n" );
        return 2;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        // report the error
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter, 1 );
        // Abc_NtkVerifyReportError( pNtk1, pNtk2, pMiter->pModel );
        ABC_FREE( pMiter->pModel );
        Abc_NtkDelete( pMiter );
        return 1;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return 0;
    }

    // convert the miter into a CNF
    pCnf = Abc_NtkMulti( pMiter, 0, 100, 1, 0, 0, 0 );
    Abc_NtkDelete( pMiter );
    if ( pCnf == NULL )
    {
        printf( "Renoding for CNF has failed.\n" );
        return 2;
    }

    // solve the CNF using the SAT solver
    RetValue = Abc_NtkMiterSat( pCnf, (ABC_INT64_T)nConfLimit, (ABC_INT64_T)nInsLimit, 0, NULL, NULL );
    // if ( RetValue == -1 )
    //     // printf( "Networks are undecided (SAT solver timed out).\n" );
    // else if ( RetValue == 0 )
    //     // printf( "Networks are NOT EQUIVALENT after SAT.\n" );
    // else
    //     // printf( "Networks are equivalent after SAT.\n" );
    // if ( pCnf->pModel )
        // Abc_NtkVerifyReportError( pNtk1, pNtk2, pCnf->pModel );
    ABC_FREE( pCnf->pModel );
    Abc_NtkDelete( pCnf );

    // TODO cleanup
    // Function does not work like I want it to so I do this
    if(RetValue == 0) {
        return 1;
    } else if(RetValue == -1) {
        return 2;
    } else {
        return 0;
    }
}

/**Function*************************************************************

  Synopsis    [Verifies sequential equivalence by fraiging followed by SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkCecFraig1( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose )
{
    abctime clk = Abc_Clock();
    Prove_Params_t Params, * pParams = &Params;
//    Fraig_Params_t Params;
//    Fraig_Man_t * pMan;
    Abc_Ntk_t * pMiter, * pTemp;
    Abc_Ntk_t * pExdc = NULL;
    int RetValue;

    if ( pNtk1->pExdc != NULL || pNtk2->pExdc != NULL )
    {
        if ( pNtk1->pExdc != NULL && pNtk2->pExdc != NULL )
        {
            printf( "Comparing EXDC of the two networks:\n" );
            Abc_NtkCecFraig1( pNtk1->pExdc, pNtk2->pExdc, nSeconds, fVerbose );
            printf( "Comparing networks under EXDC of the first network.\n" );
            pExdc = pNtk1->pExdc;
        }
        else if ( pNtk1->pExdc != NULL )
        {
            printf( "Second network has no EXDC. Comparing main networks under EXDC of the first network.\n" );
            pExdc = pNtk1->pExdc;
        }
        else if ( pNtk2->pExdc != NULL ) 
        {
            printf( "First network has no EXDC. Comparing main networks under EXDC of the second network.\n" );
            pExdc = pNtk2->pExdc;
        }
        else assert( 0 );
    }

    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 1, 0, 0, 0 );
    if ( pMiter == NULL )
    {
        printf( "Miter computation has failed.\n" );
        return 2;
    }
    // add EXDC to the miter
    if ( pExdc )
    {
        assert( Abc_NtkPoNum(pMiter) == 1 );
        assert( Abc_NtkPoNum(pExdc) == 1 );
        pMiter = Abc_NtkMiter( pTemp = pMiter, pExdc, 1, 0, 1, 0 );
        Abc_NtkDelete( pTemp );
    }
    // handle trivial case
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT after structural hashing.  " );
        // report the error
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter, 1 );
        // Abc_NtkVerifyReportError( pNtk1, pNtk2, pMiter->pModel );
        ABC_FREE( pMiter->pModel );
        Abc_NtkDelete( pMiter );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        return 1;
    }
    if ( RetValue == 1 )
    {
        printf( "Networks are equivalent after structural hashing.  " );
        Abc_NtkDelete( pMiter );
        Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
        return 0;
    }
/*
    // convert the miter into a FRAIG
    Fraig_ParamsSetDefault( &Params );
    Params.fVerbose = fVerbose;
    Params.nSeconds = nSeconds;
//    Params.fFuncRed = 0;
//    Params.nPatsRand = 0;
//    Params.nPatsDyna = 0;
    pMan = (Fraig_Man_t *)Abc_NtkToFraig( pMiter, &Params, 0, 0 ); 
    Fraig_ManProveMiter( pMan );

    // analyze the result
    RetValue = Fraig_ManCheckMiter( pMan );
    // report the result
    if ( RetValue == -1 )
        printf( "Networks are undecided (SAT solver timed out on the final miter).\n" );
    else if ( RetValue == 1 )
        printf( "Networks are equivalent after fraiging.\n" );
    else if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT after fraiging.\n" );
        Abc_NtkVerifyReportError( pNtk1, pNtk2, Fraig_ManReadModel(pMan) );
    }
    else assert( 0 );
    // delete the fraig manager
    Fraig_ManFree( pMan );
    // delete the miter
    Abc_NtkDelete( pMiter );
*/
    // solve the CNF using the SAT solver
    Prove_ParamsSetDefault( pParams );
    pParams->nItersMax = 5;
//    RetValue = Abc_NtkMiterProve( &pMiter, pParams );
//    pParams->fVerbose = 1;
    RetValue = Abc_NtkIvyProve( &pMiter, pParams );
    // if ( RetValue == -1 )
    //     printf( "Networks are undecided (resource limits is reached).  " );
    // else if ( RetValue == 0 )
    // {
    //     int * pSimInfo = Abc_NtkVerifySimulatePattern( pMiter, pMiter->pModel );
    //     if ( pSimInfo[0] != 1 )
    //         printf( "ERROR in Abc_NtkMiterProve(): Generated counter-example is invalid.\n" );
    //     else
    //         printf( "Networks are NOT EQUIVALENT.  " );
    //     ABC_FREE( pSimInfo );
    // }
    // else
    //     // printf( "Networks are equivalent.  " );
    // Abc_PrintTime( 1, "Time", Abc_Clock() - clk );
    // if ( pMiter->pModel )
    //     Abc_NtkVerifyReportError( pNtk1, pNtk2, pMiter->pModel );
    Abc_NtkDelete( pMiter );

    if(RetValue == -1) {
        return 2;
    } else if(RetValue == 0) {
        int * pSimInfo = Abc_NtkVerifySimulatePattern( pMiter, pMiter->pModel );
        if ( pSimInfo[0] != 1 ) {
            ABC_FREE( pSimInfo );
            return 2;
        }
        else {
            return 1;
            ABC_FREE( pSimInfo );
        }
    } else {
        return 0;
    }
}

/**Function*************************************************************

  Synopsis    [Verifies sequential equivalence by fraiging followed by SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkCecFraigPart1( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int nPartSize, int fVerbose )
{
    Prove_Params_t Params, * pParams = &Params;
    Abc_Ntk_t * pMiter, * pMiterPart;
    Abc_Obj_t * pObj;
    int i, RetValue, Status, nOutputs;

    // solve the CNF using the SAT solver
    Prove_ParamsSetDefault( pParams );
    pParams->nItersMax = 5;
    //    pParams->fVerbose = 1;

    assert( nPartSize > 0 );

    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 1, nPartSize, 0, 0 );
    if ( pMiter == NULL )
    {
        // printf( "Miter computation has failed.\n" );
        return 2;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
        // printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        // report the error
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter, 1 );
        // Abc_NtkVerifyReportError( pNtk1, pNtk2, pMiter->pModel );
        ABC_FREE( pMiter->pModel );
        Abc_NtkDelete( pMiter );
        return 1;
    }
    if ( RetValue == 1 )
    {
        // printf( "Networks are equivalent after structural hashing.\n" );
        Abc_NtkDelete( pMiter );
        return 0;
    }

    // Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "unset progressbar" );

    // solve the problem iteratively for each output of the miter
    Status = 1;
    nOutputs = 0;
    Abc_NtkForEachPo( pMiter, pObj, i )
    {
        if ( Abc_ObjFanin0(pObj) == Abc_AigConst1(pMiter) )
        {
            if ( Abc_ObjFaninC0(pObj) ) // complemented -> const 0
                RetValue = 1;
            else
                RetValue = 0;
            pMiterPart = NULL;
        }
        else
        {
            // get the cone of this output
            pMiterPart = Abc_NtkCreateCone( pMiter, Abc_ObjFanin0(pObj), Abc_ObjName(pObj), 0 );
            if ( Abc_ObjFaninC0(pObj) )
                Abc_ObjXorFaninC( Abc_NtkPo(pMiterPart,0), 0 );
            // solve the cone
        //    RetValue = Abc_NtkMiterProve( &pMiterPart, pParams );
            RetValue = Abc_NtkIvyProve( &pMiterPart, pParams );
        }

        if ( RetValue == -1 )
        {
            // printf( "Networks are undecided (resource limits is reached).\r" );
            Status = -1;
        }
        else if ( RetValue == 0 )
        {
            if(!pMiterPart)
            {
                // printf("ERROR: Failed to create cone for output %d.\n", i);
                Status = -1; 
                break; 
            }
            int * pSimInfo = Abc_NtkVerifySimulatePattern( pMiterPart, pMiterPart->pModel );
            if ( pSimInfo[0] != 1 )
                Status = 1;
            else
                Status = 2;
            ABC_FREE( pSimInfo );
            break;
        }
        else
        {
            // printf( "Finished part %5d (out of %5d)\r", i+1, Abc_NtkPoNum(pMiter) );
            nOutputs += nPartSize;
        }
//        if ( pMiter->pModel )
//            Abc_NtkVerifyReportError( pNtk1, pNtk2, pMiter->pModel );
        if ( pMiterPart )
            Abc_NtkDelete( pMiterPart );
    }
  
    // Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "set progressbar" );

    // if ( Status == 1 )
    //     printf( "Networks are equivalent.                         \n" );
    // else if ( Status == -1 )
    //     printf( "Timed out after verifying %d outputs (out of %d).\n", nOutputs, Abc_NtkCoNum(pNtk1) );
    Abc_NtkDelete( pMiter );

    if(Status == -1) {
        return 2;
    } else if(Status == 0) {
        return 1;
    } else {
        return 0;
    }
}

/**Function*************************************************************

  Synopsis    [Verifies sequential equivalence by fraiging followed by SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkCecFraigPartAuto1( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose )
{
    extern Vec_Ptr_t * Abc_NtkPartitionSmart( Abc_Ntk_t * pNtk, int nPartSizeLimit, int fVerbose );
    extern void Abc_NtkConvertCos( Abc_Ntk_t * pNtk, Vec_Int_t * vOuts, Vec_Ptr_t * vOnePtr );

    Vec_Ptr_t * vParts, * vOnePtr;
    Vec_Int_t * vOne;
    Prove_Params_t Params, * pParams = &Params;
    Abc_Ntk_t * pMiter, * pMiterPart;
    int i, RetValue, Status, nOutputs;

    // solve the CNF using the SAT solver
    Prove_ParamsSetDefault( pParams );
    pParams->nItersMax = 5;
    //    pParams->fVerbose = 1;

    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 1, 1, 0, 0 );
    if ( pMiter == NULL )
    {
        // printf( "Miter computation has failed.\n" );
        return 2;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
        // printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        // report the error
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter, 1 );
        // Abc_NtkVerifyReportError( pNtk1, pNtk2, pMiter->pModel );
        ABC_FREE( pMiter->pModel );
        Abc_NtkDelete( pMiter );
        return 1;
    }
    if ( RetValue == 1 )
    {
        // printf( "Networks are equivalent after structural hashing.\n" );
        Abc_NtkDelete( pMiter );
        return 0;
    }

    // Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "unset progressbar" );

    // partition the outputs
    vParts = Abc_NtkPartitionSmart( pMiter, 300, 0 );

    // fraig each partition
    Status = 1;
    nOutputs = 0;
    vOnePtr = Vec_PtrAlloc( 1000 );
    Vec_PtrForEachEntry( Vec_Int_t *, vParts, vOne, i )
    {
        // get this part of the miter
        Abc_NtkConvertCos( pMiter, vOne, vOnePtr );
        pMiterPart = Abc_NtkCreateConeArray( pMiter, vOnePtr, 0 );
        Abc_NtkCombinePos( pMiterPart, 0, 0 );
        // check the miter for being constant
        RetValue = Abc_NtkMiterIsConstant( pMiterPart );
        if ( RetValue == 0 )
        {
            printf( "Networks are NOT EQUIVALENT after partitioning.\n" );
            Abc_NtkDelete( pMiterPart );
            break;
        }
        if ( RetValue == 1 )
        {
            Abc_NtkDelete( pMiterPart );
            continue;
        }
        // printf( "Verifying part %4d  (out of %4d)  PI = %5d. PO = %5d. And = %6d. Lev = %4d.\r", 
        //     i+1, Vec_PtrSize(vParts), Abc_NtkPiNum(pMiterPart), Abc_NtkPoNum(pMiterPart), 
        //     Abc_NtkNodeNum(pMiterPart), Abc_AigLevel(pMiterPart) );
        // fflush( stdout );
        // solve the problem
        RetValue = Abc_NtkIvyProve( &pMiterPart, pParams );
        if ( RetValue == -1 )
        {
            printf( "Networks are undecided (resource limits is reached).\r" );
            Status = -1;
        }
        else if ( RetValue == 0 )
        {
            int * pSimInfo = Abc_NtkVerifySimulatePattern( pMiterPart, pMiterPart->pModel );
            if ( pSimInfo[0] != 1 )
                printf( "ERROR in Abc_NtkMiterProve(): Generated counter-example is invalid.\n" );
            else
                printf( "Networks are NOT EQUIVALENT.                 \n" );
            ABC_FREE( pSimInfo );
            Status = 0;
            Abc_NtkDelete( pMiterPart );
            break;
        }
        else
        {
//            printf( "Finished part %5d (out of %5d)\r", i+1, Vec_PtrSize(vParts) );
            nOutputs += Vec_IntSize(vOne);
        }
        Abc_NtkDelete( pMiterPart );
    }
    // printf( "                                                                                          \r" );
    Vec_VecFree( (Vec_Vec_t *)vParts );
    Vec_PtrFree( vOnePtr );

    // Cmd_CommandExecute( Abc_FrameGetGlobalFrame(), "set progressbar" );

    // if ( Status == 1 )
    //     printf( "Networks are equivalent.                         \n" );
    // else if ( Status == -1 )
    //     printf( "Timed out after verifying %d outputs (out of %d).\n", nOutputs, Abc_NtkCoNum(pNtk1) );
    Abc_NtkDelete( pMiter );

    if(Status == -1) {
        return 2;
    } else if (Status == 0) {
        return 1;
    } else {
        return 0;
    }
}

/**Function*************************************************************

  Synopsis    [Verifies sequential equivalence by brute-force SAT.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkSecSat1( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int nInsLimit, int nFrames )
{
    extern Abc_Ntk_t * Abc_NtkMulti( Abc_Ntk_t * pNtk, int nThresh, int nFaninMax, int fCnf, int fMulti, int fSimple, int fFactor );
    Abc_Ntk_t * pMiter;
    Abc_Ntk_t * pFrames;
    Abc_Ntk_t * pCnf;
    int RetValue;

    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 0, 0, 0, 0 );
    if ( pMiter == NULL )
    {
        printf( "Miter computation has failed.\n" );
        return 2;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        return 1;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return 0;
    }

    // create the timeframes
    pFrames = Abc_NtkFrames( pMiter, nFrames, 1, 0 );
    Abc_NtkDelete( pMiter );
    if ( pFrames == NULL )
    {
        printf( "Frames computation has failed.\n" );
        return 2;
    }
    RetValue = Abc_NtkMiterIsConstant( pFrames );
    if ( RetValue == 0 )
    {
        Abc_NtkDelete( pFrames );
        printf( "Networks are NOT EQUIVALENT after framing.\n" );
        return 1;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pFrames );
        printf( "Networks are equivalent after framing.\n" );
        return 0;
    }

    // convert the miter into a CNF
    pCnf = Abc_NtkMulti( pFrames, 0, 100, 1, 0, 0, 0 );
    Abc_NtkDelete( pFrames );
    if ( pCnf == NULL )
    {
        printf( "Renoding for CNF has failed.\n" );
        return 2;
    }

    // solve the CNF using the SAT solver
    RetValue = Abc_NtkMiterSat( pCnf, (ABC_INT64_T)nConfLimit, (ABC_INT64_T)nInsLimit, 0, NULL, NULL );
    Abc_NtkDelete( pCnf );
    if ( RetValue == -1 ) {
        printf( "Networks are undecided (SAT solver timed out).\n" );
        return 2;
    } else if ( RetValue == 0 ) {
        printf( "Networks are NOT EQUIVALENT after SAT.\n" );
        return 1;
    } else {
        printf( "Networks are equivalent after SAT.\n" );
        return 0;
    }
}

/**Function*************************************************************

  Synopsis    [Verifies combinational equivalence by fraiging followed by SAT]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_NtkSecFraig1( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int nFrames, int fVerbose )
{
    Fraig_Params_t Params;
    Fraig_Man_t * pMan;
    Abc_Ntk_t * pMiter;
    Abc_Ntk_t * pFrames;
    int RetValue;

    // get the miter of the two networks
    pMiter = Abc_NtkMiter( pNtk1, pNtk2, 0, 0, 0, 0 );
    if ( pMiter == NULL )
    {
        printf( "Miter computation has failed.\n" );
        return 0;
    }
    RetValue = Abc_NtkMiterIsConstant( pMiter );
    if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT after structural hashing.\n" );
        // report the error
        pMiter->pModel = Abc_NtkVerifyGetCleanModel( pMiter, nFrames );
        // Abc_NtkVerifyReportErrorSeq( pNtk1, pNtk2, pMiter->pModel, nFrames );
        ABC_FREE( pMiter->pModel );
        Abc_NtkDelete( pMiter );
        return 0;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pMiter );
        printf( "Networks are equivalent after structural hashing.\n" );
        return 1;
    }

    // create the timeframes
    pFrames = Abc_NtkFrames( pMiter, nFrames, 1, 0 );
    Abc_NtkDelete( pMiter );
    if ( pFrames == NULL )
    {
        printf( "Frames computation has failed.\n" );
        return 0;
    }
    RetValue = Abc_NtkMiterIsConstant( pFrames );
    if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT after framing.\n" );
        // report the error
        pFrames->pModel = Abc_NtkVerifyGetCleanModel( pFrames, 1 );
//        Abc_NtkVerifyReportErrorSeq( pNtk1, pNtk2, pFrames->pModel, nFrames );
        ABC_FREE( pFrames->pModel );
        Abc_NtkDelete( pFrames );
        return 0;
    }
    if ( RetValue == 1 )
    {
        Abc_NtkDelete( pFrames );
        printf( "Networks are equivalent after framing.\n" );
        return 1;
    }

    // convert the miter into a FRAIG
    Fraig_ParamsSetDefault( &Params );
    Params.fVerbose = fVerbose;
    Params.nSeconds = nSeconds;
//    Params.fFuncRed = 0;
//    Params.nPatsRand = 0;
//    Params.nPatsDyna = 0;
    pMan = (Fraig_Man_t *)Abc_NtkToFraig( pFrames, &Params, 0, 0 ); 
    Fraig_ManProveMiter( pMan );

    // analyze the result
    RetValue = Fraig_ManCheckMiter( pMan );
    // report the result
    if ( RetValue == -1 )
        printf( "Networks are undecided (SAT solver timed out on the final miter).\n" );
    else if ( RetValue == 1 )
        printf( "Networks are equivalent after fraiging.\n" );
    else if ( RetValue == 0 )
    {
        printf( "Networks are NOT EQUIVALENT after fraiging.\n" );
//        Abc_NtkVerifyReportErrorSeq( pNtk1, pNtk2, Fraig_ManReadModel(pMan), nFrames );
    }
    else assert( 0 );
    // delete the fraig manager
    Fraig_ManFree( pMan );
    // delete the miter
    Abc_NtkDelete( pFrames );
    return RetValue == 1;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END

