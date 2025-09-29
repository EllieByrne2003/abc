/**CFile****************************************************************

  FileName    [.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName []

  Synopsis    [Contains some reimplemented functions to have useful returns instead of prints]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: .c,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/

#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "proof/fraig/fraig.h"
#include "opt/fxu/fxu.h"
#include "opt/fxch/Fxch.h"
#include "opt/cut/cut.h"
#include "map/fpga/fpga.h"
#include "map/if/if.h"
#include "opt/sim/sim.h"
#include "opt/res/res.h"
#include "opt/lpk/lpk.h"
#include "aig/gia/giaAig.h"
#include "opt/dar/dar.h"
#include "opt/mfs/mfs.h"
#include "proof/fra/fra.h"
#include "aig/saig/saig.h"
#include "proof/int/int.h"
#include "proof/dch/dch.h"
#include "proof/ssw/ssw.h"
#include "opt/cgt/cgt.h"
#include "bool/kit/kit.h"
#include "map/amap/amap.h"
#include "opt/ret/retInt.h"
#include "sat/xsat/xsat.h"
#include "sat/satoko/satoko.h"
#include "sat/cnf/cnf.h"
#include "proof/cec/cec.h"
#include "proof/acec/acec.h"
#include "proof/pdr/pdr.h"
#include "misc/tim/tim.h"
#include "bdd/llb/llb.h"
#include "bdd/bbr/bbr.h"
#include "map/cov/cov.h"
#include "base/cmd/cmd.h"
#include "proof/abs/abs.h"
#include "sat/bmc/bmc.h"
#include "proof/ssc/ssc.h"
#include "opt/sfm/sfm.h"
#include "opt/sbd/sbd.h"
#include "bool/rpo/rpo.h"
#include "map/mpm/mpm.h"
#include "map/mio/mio.h"
#include "opt/fret/fretime.h"
#include "opt/nwk/nwkMerge.h"
#include "base/acb/acbPar.h"
#include "misc/extra/extra.h"
#include "opt/eslim/eSLIM.h"

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

  Synopsis    [Compares whether networks are equivalent]

  Description [By default, checks pAbc net as is with it's starting]

  SideEffects []

  SeeAlso     []

***********************************************************************/
int Abc_ApiCec( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    char Buffer[16];
    Abc_Ntk_t * pNtk, * pNtk1, * pNtk2;
    int fDelete1, fDelete2;
    char ** pArgvNew;
    int nArgcNew;
    int c;
    int fSat;
    int fVerbose;
    int nSeconds;
    int nPartSize;
    int nConfLimit;
    int nInsLimit;
    int fPartition;
    int fIgnoreNames;

    extern int Abc_NtkCecSat1( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nConfLimit, int nInsLimit );
    extern int Abc_NtkCecFraig1( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose );
    extern int Abc_NtkCecFraigPart1( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int nPartSize, int fVerbose );
    extern int Abc_NtkCecFraigPartAuto1( Abc_Ntk_t * pNtk1, Abc_Ntk_t * pNtk2, int nSeconds, int fVerbose );

    pNtk = Abc_FrameReadNtk(pAbc);
    // set defaults
    fSat     =  0;
    fVerbose =  0;
    nSeconds = 20;
    nPartSize  = 0;
    nConfLimit = 10000;
    nInsLimit  = 0;
    fPartition = 0;
    fIgnoreNames = 0;
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "TCIPpsnvh" ) ) != EOF )
    {
        switch ( c )
        {
        case 'T':
            if ( globalUtilOptind >= argc )
            {
                // Abc_Print( -1, "Command line switch \"-T\" should be followed by an integer.\n" );
                goto usage;
            }
            nSeconds = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nSeconds < 0 )
                goto usage;
            break;
        case 'C':
            if ( globalUtilOptind >= argc )
            {
                // Abc_Print( -1, "Command line switch \"-C\" should be followed by an integer.\n" );
                goto usage;
            }
            nConfLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nConfLimit < 0 )
                goto usage;
            break;
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                // Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            nInsLimit = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nInsLimit < 0 )
                goto usage;
            break;
        case 'P':
            if ( globalUtilOptind >= argc )
            {
                // Abc_Print( -1, "Command line switch \"-P\" should be followed by an integer.\n" );
                goto usage;
            }
            nPartSize = atoi(argv[globalUtilOptind]);
            globalUtilOptind++;
            if ( nPartSize < 0 )
                goto usage;
            break;
        case 'p':
            fPartition ^= 1;
            break;
        case 's':
            fSat ^= 1;
            break;
        case 'n':
            fIgnoreNames ^= 1;
            break;
        case 'v':
            fVerbose ^= 1;
            break;
        default:
            goto usage;
        }
    }

    if ( pNtk && pNtk->vPhases != NULL )
    {
        // Abc_Print( -1, "Cannot compare networks with phases defined.\n" );
        return 2;
    }

    pArgvNew = argv + globalUtilOptind;
    nArgcNew = argc - globalUtilOptind;
    if ( !Abc_NtkPrepareTwoNtks( stdout, pNtk, pArgvNew, nArgcNew, &pNtk1, &pNtk2, &fDelete1, &fDelete2, 1 ) )
        return 2;

    if ( fIgnoreNames )
    {
        if ( !fDelete1 )
        {
            pNtk1 = Abc_NtkStrash( pNtk1, 0, 1, 0 );
            fDelete1 = 1;
        }
        if ( !fDelete2 )
        {
            pNtk2 = Abc_NtkStrash( pNtk2, 0, 1, 0 );
            fDelete2 = 1;
        }
        Abc_NtkShortNames( pNtk1 );
        Abc_NtkShortNames( pNtk2 );
    }

    int retValue;

    // perform equivalence checking
    if ( fPartition )
        retValue = Abc_NtkCecFraigPartAuto1( pNtk1, pNtk2, nSeconds, fVerbose );
    else if ( nPartSize )
        retValue = Abc_NtkCecFraigPart1( pNtk1, pNtk2, nSeconds, nPartSize, fVerbose );
    else if ( fSat )
        retValue = Abc_NtkCecSat1( pNtk1, pNtk2, nConfLimit, nInsLimit );
    else
        retValue = Abc_NtkCecFraig1( pNtk1, pNtk2, nSeconds, fVerbose );

    if ( fDelete1 ) Abc_NtkDelete( pNtk1 );
    if ( fDelete2 ) Abc_NtkDelete( pNtk2 );
    return retValue;

usage:
    if ( nPartSize == 0 )
        strcpy( Buffer, "unused" );
    else
        sprintf(Buffer, "%d", nPartSize );
    // Abc_Print( -2, "usage: cec [-T num] [-C num] [-I num] [-P num] [-psnvh] <file1> <file2>\n" );
    // Abc_Print( -2, "\t         performs combinational equivalence checking\n" );
    // Abc_Print( -2, "\t-T num : approximate runtime limit in seconds [default = %d]\n", nSeconds );
    // Abc_Print( -2, "\t-C num : limit on the number of conflicts [default = %d]\n",    nConfLimit );
    // Abc_Print( -2, "\t-I num : limit on the number of clause inspections [default = %d]\n", nInsLimit );
    // Abc_Print( -2, "\t-P num : partition size for multi-output networks [default = %s]\n", Buffer );
    // Abc_Print( -2, "\t-p     : toggle automatic partitioning [default = %s]\n", fPartition? "yes": "no" );
    // Abc_Print( -2, "\t-s     : toggle \"SAT only\" and \"FRAIG + SAT\" [default = %s]\n", fSat? "SAT only": "FRAIG + SAT" );
    // Abc_Print( -2, "\t-n     : toggle how CIs/COs are matched (by name or by order) [default = %s]\n", fIgnoreNames? "by order": "by name" );
    // Abc_Print( -2, "\t-v     : toggle verbose output [default = %s]\n", fVerbose? "yes": "no" );
    // Abc_Print( -2, "\t-h     : print the command usage\n");
    // Abc_Print( -2, "\tfile1  : (optional) the file with the first network\n");
    // Abc_Print( -2, "\tfile2  : (optional) the file with the second network\n");
    // Abc_Print( -2, "\t         if no files are given, uses the current network and its spec\n");
    // Abc_Print( -2, "\t         if one file is given, uses the current network and the file\n");
    return 2;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END
