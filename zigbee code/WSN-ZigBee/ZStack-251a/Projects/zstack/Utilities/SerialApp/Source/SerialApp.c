/*********************************************************************
* INCLUDES
*/
#include <stdio.h>
#include <string.h>

#include "AF.h"
#include "OnBoard.h"
#include "OSAL_Tasks.h"
#include "SerialApp.h"
#include "ZDApp.h"
#include "ZDObject.h"
#include "ZDProfile.h"

#include "hal_drivers.h"
#include "hal_key.h"
#if defined ( LCD_SUPPORTED )
#include "hal_lcd.h"
#endif
#include "hal_led.h"
#include "hal_uart.h"

#include "DHT11.h"
#include "nwk_globals.h"


//---------------------------------------------------------------------
//��׼�治ͬ���ն���Ҫ�޸Ĵ�ID,����ʶ��Э���������������ݣ�ID��ͬ����
static uint16 EndDeviceID = 0x0001 ; //�ն�ID����Ҫ
//---------------------------------------------------------------------

//����ڵ㹦������������������+������,���ǲ������
#define WSN_SENSOR     //����4���ɼ��ڵ�
//#define WSN_BEEP     //����+������ EndDeviceID=5
//#define WSN_STEP     //�������    EndDeviceID=6



#define LAMP_PIN     P0_5  //����P0.5��Ϊ�̵��������
#define GAS_PIN      P0_6  //����P0.6��Ϊ���������������  
#define BEEP_PIN     P0_7  //����P0.7��Ϊ�������������  

#define A1 P0_4            //���岽��������Ӷ˿�
#define B1 P0_5
#define C1 P0_6
#define D1 P0_7


#define UART0        0x00
#define MAX_NODE     0x04
#define UART_DEBUG   0x00 //���Ժ�,ͨ���������Э�������ն˵�IEEE���̵�ַ
#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof(arr)[0])

#define TIMER1_RUN()  T1CTL|=0X03
#define TIMER1_STOP() T1CTL&=~0X03
/*********************************************************************
* CONSTANTS
*/

#if !defined( SERIAL_APP_PORT )
#define SERIAL_APP_PORT  0
#endif

#if !defined( SERIAL_APP_BAUD )
#define SERIAL_APP_BAUD  HAL_UART_BR_115200  //HAL_UART_BR_38400
#endif

// When the Rx buf space is less than this threshold, invoke the Rx callback.
#if !defined( SERIAL_APP_THRESH )
#define SERIAL_APP_THRESH  64
#endif

#if !defined( SERIAL_APP_RX_SZ )
#define SERIAL_APP_RX_SZ  128
#endif

#if !defined( SERIAL_APP_TX_SZ )
#define SERIAL_APP_TX_SZ  128
#endif

// Millisecs of idle time after a byte is received before invoking Rx callback.
#if !defined( SERIAL_APP_IDLE )
#define SERIAL_APP_IDLE  6
#endif

// Loopback Rx bytes to Tx for throughput testing.
#if !defined( SERIAL_APP_LOOPBACK )
#define SERIAL_APP_LOOPBACK  FALSE
#endif

// This is the max byte count per OTA message.
#if !defined( SERIAL_APP_TX_MAX )
#define SERIAL_APP_TX_MAX  20
#endif

#define SERIAL_APP_RSP_CNT  4

// This list should be filled with Application specific Cluster IDs.
const cId_t SerialApp_ClusterList[SERIALAPP_MAX_CLUSTERS] =
{
  SERIALAPP_CLUSTERID
};

const SimpleDescriptionFormat_t SerialApp_SimpleDesc =
{
  SERIALAPP_ENDPOINT,              //  int   Endpoint;
  SERIALAPP_PROFID,                //  uint16 AppProfId[2];
  SERIALAPP_DEVICEID,              //  uint16 AppDeviceId[2];
  SERIALAPP_DEVICE_VERSION,        //  int   AppDevVer:4;
  SERIALAPP_FLAGS,                 //  int   AppFlags:4;
  SERIALAPP_MAX_CLUSTERS,          //  byte  AppNumInClusters;
  (cId_t *)SerialApp_ClusterList,  //  byte *pAppInClusterList;
  SERIALAPP_MAX_CLUSTERS,          //  byte  AppNumOutClusters;
  (cId_t *)SerialApp_ClusterList   //  byte *pAppOutClusterList;
};

const endPointDesc_t SerialApp_epDesc =
{
  SERIALAPP_ENDPOINT,
  &SerialApp_TaskID,
  (SimpleDescriptionFormat_t *)&SerialApp_SimpleDesc,
  noLatencyReqs
};


/*********************************************************************
* GLOBAL VARIABLES
*/
uint8 AppTitle[20] = "FHP WSN-system"; //Ӧ�ó�������
uint8 SerialApp_TaskID;    // Task ID for internal task/event processing.


/*********************************************************************
* LOCAL VARIABLES
*/
#ifdef WSN_SENSOR
static bool SendFlag = 0;
#endif
static uint8 SerialApp_MsgID;

static afAddrType_t SerialApp_TxAddr;
static afAddrType_t Broadcast_DstAddr;

static uint8 SerialApp_TxSeq;
static uint8 SerialApp_TxBuf[SERIAL_APP_TX_MAX+1];
static uint8 SerialApp_TxLen;

static afAddrType_t SerialApp_RxAddr;
static uint8 SerialApp_RspBuf[SERIAL_APP_RSP_CNT];

static devStates_t SerialApp_NwkState;
static afAddrType_t SerialApp_TxAddr;
static uint8 SerialApp_MsgID;

uint8 NodeData[MAX_NODE][5];         //�ն����ݻ����� 0=�¶� 1=ʪ�� 2=���� 3=��
uint8 TxBuffer[128];

//�����صı���
uint8 LedState = 0;
uint8 ucEdDir = 1;      //�ն�1Ϊ��ת  2Ϊ��ת
uint8 ucDirection = 1;  //1Ϊ��ת  2Ϊ��ת
uint8 ucSpeed = 2;      //�ٶ�2-10֮��
uint8 DataBuf[3];

uchar phasecw[4] ={0x80,0x40,0x20,0x10};//��ת �����ͨ���� D-C-B-A
uchar phaseccw[4]={0x10,0x20,0x40,0x80};//��ת �����ͨ���� A-B-C-D
/*********************************************************************
* LOCAL FUNCTIONS
*/

static void SerialApp_HandleKeys( uint8 shift, uint8 keys );
static void SerialApp_ProcessMSGCmd( afIncomingMSGPacket_t *pkt );
static void SerialApp_Send(void);
static void SerialApp_Resp(void);
static void SerialApp_CallBack(uint8 port, uint8 event);

#if UART_DEBUG  
static void GetIeeeAddr(uint8 * pIeeeAddr, uint8 *pStr);
static void PrintAddrInfo(uint16 shortAddr, uint8 *pIeeeAddr);
#endif
static void AfSendAddrInfo(void);
static void SerialApp_SendPeriodicMessage( void );
static uint8 GetDataLen(uint8 fc);
static uint8 GetLamp( void );
static uint8 GetGas( void );
static uint8 XorCheckSum(uint8 * pBuf, uint8 len);
uint8 SendData(uint8 addr, uint8 FC);

//WSN_BEEP
void init_timer(void);
void init_port(void);
void start_pwm(void) ;
__interrupt void _IRQ_timer1(void);

//WSN_STEP
static void MotorData(uchar data);
static void MotorCW(void);
static void MotorCCW(void);
static void MotorStop(void);

static void Delay_MS(unsigned int Time);
#ifdef WSN_STEP
static void InitStepMotor(void);
#endif
/*********************************************************************
* @fn      SerialApp_Init
*
* @brief   This is called during OSAL tasks' initialization.
*
* @param   task_id - the Task ID assigned by OSAL.
*
* @return  none
*/
void SerialApp_Init( uint8 task_id )
{
  halUARTCfg_t uartConfig;
  
#ifdef WSN_SENSOR
  P0SEL &= ~0x20;         //����P0.5��Ϊ��ͨIO
  P0DIR |= 0x20;          //����P0.5Ϊ���
  LAMP_PIN = 1;           //�ߵ�ƽ�̵����Ͽ�;�͵�ƽ�̵�������
  P0SEL &= ~0x40;         //����P0.6Ϊ��ͨIO��
  P0DIR &= ~0x40;         //P0.6����Ϊ�����
  P0SEL &= ~0x80;         //P0_7���ó�ͨ��io
#elif defined WSN_BEEP
  P0SEL &= ~0x40;         //����P0.6Ϊ��ͨIO��
  P0DIR &= ~0x40;         //P0.6����Ϊ�����
  start_pwm();            //����T1���PWM
  TIMER1_STOP();          //Ĭ�Ϲرշ�����
  EndDeviceID = 0x0005;   //�ն�5���ڲ����  
#elif defined WSN_STEP
  InitStepMotor();        //��ʼ�����IO����
  EndDeviceID = 0x0006;   //�ն�6���ڲ����  
#endif

#if defined(ZDO_COORDINATOR) 
  EndDeviceID = 0x0000; 
#endif
  
  Color    = BLACK; //ǰ��ɫ
  Color_BK = GREEN; //����ɫ
  osal_memset(AppTitle, 0, 20);
  //LCD����ʾӦ�ó���ı���
  if(EndDeviceID == 0x0001)
    osal_memcpy(AppTitle, "ALD WSN-Node01", osal_strlen("ALD WSN-Node01"));
  else if(EndDeviceID == 0x0002)
    osal_memcpy(AppTitle, "ALD WSN-Node02", osal_strlen("ALD WSN-Node02"));
  else if(EndDeviceID == 0x0003)
    osal_memcpy(AppTitle, "ALD WSN-Node03", osal_strlen("ALD WSN-Node03"));
  else if(EndDeviceID == 0x0004)
    osal_memcpy(AppTitle, "ALD WSN-Node04", osal_strlen("ALD WSN-Node04"));
  else if(EndDeviceID == 0x0005)
    osal_memcpy(AppTitle, "ALD WSN-BEEP05", osal_strlen("ALD WSN-BEEP05"));    
  else if(EndDeviceID == 0x0006)
    osal_memcpy(AppTitle, "stepping motor", osal_strlen("stepping motor")); 
  else
    osal_memcpy(AppTitle, "ALD WSN-system", osal_strlen("ALD WSN-system")); 
  
  LCD_write_EN_string(64-7*osal_strlen((char *)AppTitle)/2,3,AppTitle); //��ʾ����
  
  SerialApp_TaskID = task_id;
  //SerialApp_RxSeq = 0xC3;
  afRegister( (endPointDesc_t *)&SerialApp_epDesc );
  RegisterForKeys( task_id );
  
  uartConfig.configured           = TRUE;              // 2x30 don't care - see uart driver.
  uartConfig.baudRate             = SERIAL_APP_BAUD;
  uartConfig.flowControl          = FALSE;
  uartConfig.flowControlThreshold = SERIAL_APP_THRESH; // 2x30 don't care - see uart driver.
  uartConfig.rx.maxBufSize        = SERIAL_APP_RX_SZ;  // 2x30 don't care - see uart driver.
  uartConfig.tx.maxBufSize        = SERIAL_APP_TX_SZ;  // 2x30 don't care - see uart driver.
  uartConfig.idleTimeout          = SERIAL_APP_IDLE;   // 2x30 don't care - see uart driver.
  uartConfig.intEnable            = TRUE;              // 2x30 don't care - see uart driver.
  uartConfig.callBackFunc         = SerialApp_CallBack;
  HalUARTOpen (UART0, &uartConfig);
  
  //#if defined ( LCD_SUPPORTED )
  //  HalLcdWriteString( "SerialApp", HAL_LCD_LINE_2 );
  //#endif
  //HalUARTWrite(UART0, "Init", 4);
  //ZDO_RegisterForZDOMsg( SerialApp_TaskID, End_Device_Bind_rsp );
  //ZDO_RegisterForZDOMsg( SerialApp_TaskID, Match_Desc_rsp );
}

/*********************************************************************
* @fn      SerialApp_ProcessEvent
*
* @brief   Generic Application Task event processor.
*
* @param   task_id  - The OSAL assigned task ID.
* @param   events   - Bit map of events to process.
*
* @return  Event flags of all unprocessed events.
*/
UINT16 SerialApp_ProcessEvent( uint8 task_id, UINT16 events )
{
  (void)task_id;  // Intentionally unreferenced parameter
  
  if ( events & SYS_EVENT_MSG )
  {
    afIncomingMSGPacket_t *MSGpkt;
    
    while ( (MSGpkt = (afIncomingMSGPacket_t *)osal_msg_receive( SerialApp_TaskID )) )
    {
      switch ( MSGpkt->hdr.event )
      {
      case ZDO_CB_MSG:
        //SerialApp_ProcessZDOMsgs( (zdoIncomingMsg_t *)MSGpkt );
        break;
        
      case KEY_CHANGE:
        SerialApp_HandleKeys( ((keyChange_t *)MSGpkt)->state, ((keyChange_t *)MSGpkt)->keys );
        break;
        
      case AF_INCOMING_MSG_CMD:
        SerialApp_ProcessMSGCmd( MSGpkt );
        break;
        
      case ZDO_STATE_CHANGE:
        SerialApp_NwkState = (devStates_t)(MSGpkt->hdr.status);
        if ( (SerialApp_NwkState == DEV_ZB_COORD)
            || (SerialApp_NwkState == DEV_ROUTER)
              || (SerialApp_NwkState == DEV_END_DEVICE) )
        {
#if defined(ZDO_COORDINATOR) //Э����ͨ�������������̵�ַ��IEEE  
          Broadcast_DstAddr.addrMode = (afAddrMode_t)AddrBroadcast;
          Broadcast_DstAddr.endPoint = SERIALAPP_ENDPOINT;
          Broadcast_DstAddr.addr.shortAddr = 0xFFFF;
#if UART_DEBUG           
          PrintAddrInfo( NLME_GetShortAddr(), aExtendedAddress + Z_EXTADDR_LEN - 1);
#endif 
          //��ʼ���Ƶ�״̬��1ΪϨ��״̬��0Ϊ����
          NodeData[0][3] = 1;
          NodeData[1][3] = 1;
          NodeData[2][3] = 1;
          NodeData[3][3] = 1;
#else                        //�ն����߷��Ͷ̵�ַ��IEEE   
          AfSendAddrInfo();
#ifdef WSN_BEEP              //������������ʵ��ʱ�Զ�������巢���쳣�ͱ���
          osal_start_timerEx( SerialApp_TaskID, SERIALAPP_SEND_PERIODIC_EVT,
                             SERIALAPP_SEND_PERIODIC_TIMEOUT );
          //(SERIALAPP_SEND_PERIODIC_TIMEOUT + (osal_rand() & 0x00FF)) );
#endif
          
#endif
        }
        break;				
      default:
        break;
      }
      
      osal_msg_deallocate( (uint8 *)MSGpkt );
    }
    
    return ( events ^ SYS_EVENT_MSG );
  }
  
  //�ڴ��¼��п��Զ�ʱ��Э�������ͽڵ㴫����������Ϣ
  if ( events & SERIALAPP_SEND_PERIODIC_EVT )
  {
    SerialApp_SendPeriodicMessage();
    
    osal_start_timerEx( SerialApp_TaskID, SERIALAPP_SEND_PERIODIC_EVT,
                       (SERIALAPP_SEND_PERIODIC_TIMEOUT + (osal_rand() & 0x00FF)) );
    
    return (events ^ SERIALAPP_SEND_PERIODIC_EVT);
  }
  
  if ( events & SERIALAPP_SEND_EVT )
  {
    SerialApp_Send();
    return ( events ^ SERIALAPP_SEND_EVT );
  }
  
  if ( events & SERIALAPP_RESP_EVT )
  {
    SerialApp_Resp();
    return ( events ^ SERIALAPP_RESP_EVT );
  }
  
  return ( 0 ); 
}

/*********************************************************************
* @fn      SerialApp_HandleKeys
*
* @brief   Handles all key events for this device.
*
* @param   shift - true if in shift/alt.
* @param   keys  - bit field for key events.
*
* @return  none
*/
void SerialApp_HandleKeys( uint8 shift, uint8 keys )
{ 
  if ( keys & HAL_KEY_SW_6 ) //��S1��������ֹͣ�ն˶�ʱ�ϱ����� 
  {
#ifdef WSN_SENSOR
    if(SendFlag == 0)
    {
      SendFlag = 1;
      HalLedSet ( HAL_LED_1, HAL_LED_MODE_ON );
      osal_start_timerEx( SerialApp_TaskID,
                         SERIALAPP_SEND_PERIODIC_EVT,
                         SERIALAPP_SEND_PERIODIC_TIMEOUT );
    }
    else
    {      
      SendFlag = 0;
      HalLedSet ( HAL_LED_1, HAL_LED_MODE_OFF );
      osal_stop_timerEx(SerialApp_TaskID, SERIALAPP_SEND_PERIODIC_EVT);
    }
#endif
  }
  
  if ( keys & HAL_KEY_SW_1 ) //��S2
  {
    LAMP_PIN = ~LAMP_PIN;
  }
  
}

void SerialApp_ProcessMSGCmd( afIncomingMSGPacket_t *pkt )
{
  uint16 i, shortAddr;
  uint8 *pIeeeAddr; 
  uint8 delay;
  uint8 afRxData[30]={0};
  
  //��ѯ�����ն������д����������� 3A 00 01 02 39 23  ��Ӧ��3A 00 01 02 00 00 00 00 xor 23
  switch ( pkt->clusterId )
  {
    // A message with a serial data block to be transmitted on the serial port.
  case SERIALAPP_CLUSTERID:
    osal_memcpy(afRxData, pkt->cmd.Data, pkt->cmd.DataLength);
    switch(afRxData[0]) //��Э�������ֽ���
    {
#if defined(ZDO_COORDINATOR)
    case 0x3B:  //�յ��ն����߷������Ķ̵�ַ��IEEE��ַ,ͨ�����������ʾ      
      shortAddr=(afRxData[1]<<8)|afRxData[2];
      pIeeeAddr = &afRxData[3];
#if UART_DEBUG
      PrintAddrInfo(shortAddr, pIeeeAddr + Z_EXTADDR_LEN - 1);
#endif   
      break;
    case 0x3A:	
      if(afRxData[3] == 0x02) //�յ��ն˴������Ĵ��������ݲ�����
      {  
        NodeData[afRxData[2]-1][0] = afRxData[4];
        NodeData[afRxData[2]-1][1] = afRxData[5];
        NodeData[afRxData[2]-1][2] = afRxData[6];
        NodeData[afRxData[2]-1][3] = afRxData[7];
        NodeData[afRxData[2]-1][4] = 0x00;
      }
      
#if UART_DEBUG
      HalUARTWrite (UART0, NodeData[afRxData[3]-1], 4); //����ʱͨ���������
      HalUARTWrite (UART0, "\n", 1);
#endif            
      break;
#else  
    case 0x3A:  //���ص��豸          
      if(afRxData[3] == 0x0A || afRxData[3] == 0x0B || afRxData[3] == 0x0C) //�����ն�          
      {  
        if(EndDeviceID == afRxData[2] || afRxData[2]==0xFF)
        {
          if(afRxData[4] == 0)
          {
            LAMP_PIN = 0;
            HalLedSet ( HAL_LED_2, HAL_LED_MODE_OFF );
          }
          else
          {
            LAMP_PIN = 1;
            HalLedSet ( HAL_LED_2, HAL_LED_MODE_ON );
          }
        }
        break;
      }	
      else if(afRxData[3] == 0x07)      //������ ������Ϊ07
      {
        if(EndDeviceID == afRxData[2] || afRxData[2] == 0xFF)  //������ EndDeviceIDΪ05
        {
          if(afRxData[4] == 0)
          {
            TIMER1_STOP();               //�յ�Э�������ķ����������ָ��
            HalLedSet ( HAL_LED_2, HAL_LED_MODE_OFF );
          }
          else
          {
            TIMER1_RUN();               //�յ�Э�������ķ��������ָ��
            HalLedSet ( HAL_LED_2, HAL_LED_MODE_ON );
          }
        } 
      }
      else if(afRxData[3] == 0x08)    //��� ������Ϊ08
      {
        if(EndDeviceID == afRxData[2] || afRxData[2] == 0xFF)//��� EndDeviceIDΪ06
        {
          ucEdDir = afRxData[4];      //������ת�����������
          MotorStop();                //ֹͣת��
          if(afRxData[4] == 0x02)   
          {
            for(i=0;i<2000;i++)
              MotorCW();              //˳ʱ��ת��
          }
          else if(afRxData[4] == 0x01)//��ת��� 
          {
            for(i=0;i<2000;i++)
              MotorCCW();             //��ʱ��ת��
          }
        }
      }
#endif
      default :
        break;
      }
      break;
      // A response to a received serial data block.
    case SERIALAPP_CLUSTERID2:
      if ((pkt->cmd.Data[1] == SerialApp_TxSeq) &&
          ((pkt->cmd.Data[0] == OTA_SUCCESS) || (pkt->cmd.Data[0] == OTA_DUP_MSG)))
      {
        SerialApp_TxLen = 0;
        osal_stop_timerEx(SerialApp_TaskID, SERIALAPP_SEND_EVT);
      }
      else
      {
        // Re-start timeout according to delay sent from other device.
        delay = BUILD_UINT16( pkt->cmd.Data[2], pkt->cmd.Data[3] );
        osal_start_timerEx( SerialApp_TaskID, SERIALAPP_SEND_EVT, delay );
      }
      break;
      
    default:
      break;
    }
  }
  
uint8 SendData(uint8 addr, uint8 FC)
{
  uint8 ret, i, index=4;
  
  TxBuffer[0] = 0x3A;
  TxBuffer[1] = 0x00;
  TxBuffer[2] = addr;
  TxBuffer[3] = FC;
  
  switch(FC)
  {
  case 0x01: //��ѯ�����ն˴�����������
    for (i=0; i<MAX_NODE; i++)
    {
      osal_memcpy(&TxBuffer[index], NodeData[i], 4);
      index += 4;
    }
    TxBuffer[index] = XorCheckSum(TxBuffer, index);
    TxBuffer[index+1] = 0x23; 
    
    HalUARTWrite(UART0, TxBuffer, index+2);
    ret = 1;
    break;
  case 0x02: //��ѯ�����ն������д�����������
    osal_memcpy(&TxBuffer[index], NodeData[addr-1], 4);
    index += 4;
    TxBuffer[index] = XorCheckSum(TxBuffer, index);
    TxBuffer[index+1] = 0x23; 
    
    HalUARTWrite(UART0, TxBuffer, index+2);		
    ret = 1;
    break;   
  default:
    ret = 0;
    break;
  }
  
  return ret;
}

/*********************************************************************
* @fn      SerialApp_Send
*
* @brief   Send data OTA.
*
* @param   none
*  3A000507013923    3A 00 01 01 3A 23
* @return  none
*/
#pragma optimize=none  
static void SerialApp_Send(void)
{
  uint8 len=0, addr, FC;
  uint8 checksum=0;

  if (!SerialApp_TxLen && 
      (SerialApp_TxLen = HalUARTRead(UART0, SerialApp_TxBuf, SERIAL_APP_TX_MAX)))
  {
    if (SerialApp_TxLen)
    {
      SerialApp_TxLen = 0;
      if(SerialApp_TxBuf[0] == 0x3A)
      {
        addr = SerialApp_TxBuf[2];
        FC = SerialApp_TxBuf[3];
        len = GetDataLen(FC); 
        len += 4;
        checksum = XorCheckSum(SerialApp_TxBuf, len);

        //����������ȷ������Ӧ����
        if(checksum == SerialApp_TxBuf[len] && SerialApp_TxBuf[len+1] == 0x23)
        {
          if(FC == 7 || FC == 8 || FC == 0x0A || FC == 0x0B || FC == 0x0C) //�����ն�
          {                            
            if (afStatus_SUCCESS == AF_DataRequest(&Broadcast_DstAddr,
                                                   (endPointDesc_t *)&SerialApp_epDesc,
                                                   SERIALAPP_CLUSTERID,
                                                   len+2, SerialApp_TxBuf,
                                                   &SerialApp_MsgID, 0, AF_DEFAULT_RADIUS))
            {
              if(FC == 0x0A) //��������Զ�ˢ������Ҫ�ⲽ����
                NodeData[addr-1][3] = SerialApp_TxBuf[len-1];  //���»������Ƶ�״̬
              
              HalUARTWrite(UART0, SerialApp_TxBuf, len+2); //���߷��ͳɹ���ԭ�����ظ���λ��	
              //osal_set_event(SerialApp_TaskID, SERIALAPP_SEND_EVT);
            }
            else  //��ʱû���ִ��󣬹ر��ն˷���Ҳ���������߷���ʧ�ܺ�����λ��У��λ��0������λ��	
            {
              SerialApp_TxBuf[len-1] = 0x00;
              SerialApp_TxBuf[len] = 0x00;
              HalUARTWrite(UART0, SerialApp_TxBuf, len+2);
            }
          }
          else
          {
            SendData(addr, FC);   //��ѯ����
          }
        }
      }
    }
  }
}

/*********************************************************************
* @fn      SerialApp_Resp
*
* @brief   Send data OTA.
*
* @param   none
*
* @return  none
*/
static void SerialApp_Resp(void)
{
  if (afStatus_SUCCESS != AF_DataRequest(&SerialApp_RxAddr,
                                         (endPointDesc_t *)&SerialApp_epDesc,
                                         SERIALAPP_CLUSTERID2,
                                         SERIAL_APP_RSP_CNT, SerialApp_RspBuf,
                                         &SerialApp_MsgID, 0, AF_DEFAULT_RADIUS))
  {
    osal_set_event(SerialApp_TaskID, SERIALAPP_RESP_EVT);
  }
}

/*********************************************************************
* @fn      SerialApp_CallBack
*
* @brief   Send data OTA.
*
* @param   port - UART port.
* @param   event - the UART port event flag.
*
* @return  none
*/
static void SerialApp_CallBack(uint8 port, uint8 event)
{
  (void)port;
  
  if ((event & (HAL_UART_RX_FULL | HAL_UART_RX_ABOUT_FULL | HAL_UART_RX_TIMEOUT)) &&
#if SERIAL_APP_LOOPBACK
      (SerialApp_TxLen < SERIAL_APP_TX_MAX))
#else
    !SerialApp_TxLen)
#endif
  {
    SerialApp_Send();
  }
}


//--------------------------------------------------------------------------------------
//��ѯ�����ն������д����������� 3A 00 01 02 XX 23  ��Ӧ��3A 00 01 02 00 00 00 00 xor 23
void SerialApp_SendPeriodicMessage( void )
{
  uint8 SendBuf[11]={0};

#ifdef WSN_SENSOR  
  SendBuf[0] = 0x3A;                          
  SendBuf[1] = HI_UINT16( EndDeviceID );
  SendBuf[2] = LO_UINT16( EndDeviceID );
  SendBuf[3] = 0x02;                       //FC
  
  DHT11();                //��ȡ��ʪ��
  SendBuf[4] = wendu;  
  SendBuf[5] = shidu;  
  SendBuf[6] = GetGas();  //��ȡ���崫������״̬  
  SendBuf[7] = GetLamp(); //��õƵ�״̬
  SendBuf[8] = XorCheckSum(SendBuf, 9);
  SendBuf[9] = 0x23;
  
  SerialApp_TxAddr.addrMode = (afAddrMode_t)Addr16Bit;
  SerialApp_TxAddr.endPoint = SERIALAPP_ENDPOINT;
  SerialApp_TxAddr.addr.shortAddr = 0x00;  
  if ( AF_DataRequest( &SerialApp_TxAddr, (endPointDesc_t *)&SerialApp_epDesc,
                      SERIALAPP_CLUSTERID,
                      10,
                      SendBuf,
                      &SerialApp_MsgID, 
                      0, 
                      AF_DEFAULT_RADIUS ) == afStatus_SUCCESS )
  {
    // Successfully requested to be sent.
  }
  else
  {
    // Error occurred in request to send.
  }
#endif
  
#ifdef WSN_BEEP
  SendBuf[0] = GetGas();  //��ȡ���崫������״̬ 0Ϊ�к�����   1Ϊ����
  
  //�ն�5ִ�з���������   ������������ƽ 1: �� ��0: ����
  if(SendBuf[0] == 0 && EndDeviceID == 5)
  {
    TIMER1_RUN();      //��⵽�쳣����ʱ��������
  }
  else
  {
    TIMER1_STOP();    //������������
  }    
#endif
}


#if UART_DEBUG   
//ͨ����������̵�ַ IEEE
void PrintAddrInfo(uint16 shortAddr, uint8 *pIeeeAddr)
{
  uint8 strIeeeAddr[17] = {0};
  char  buff[30] = {0};    
  
  //��ö̵�ַ   
  sprintf(buff, "shortAddr:%04X   IEEE:", shortAddr);  
  
  //���IEEE��ַ
  GetIeeeAddr(pIeeeAddr, strIeeeAddr);
  
  HalUARTWrite (UART0, (uint8 *)buff, strlen(buff));
  Delay_ms(10);
  HalUARTWrite (UART0, strIeeeAddr, 16); 
  HalUARTWrite (UART0, "\n", 1);
}

void GetIeeeAddr(uint8 * pIeeeAddr, uint8 *pStr)
{
  uint8 i;
  uint8 *xad = pIeeeAddr;
  
  for (i = 0; i < Z_EXTADDR_LEN*2; xad--)
  {
    uint8 ch;
    ch = (*xad >> 4) & 0x0F;
    *pStr++ = ch + (( ch < 10 ) ? '0' : '7');
    i++;
    ch = *xad & 0x0F;
    *pStr++ = ch + (( ch < 10 ) ? '0' : '7');
    i++;
  }
}
#endif  

void AfSendAddrInfo(void)
{
  uint16 shortAddr;
  uint8 strBuf[11]={0};  
  
  SerialApp_TxAddr.addrMode = (afAddrMode_t)Addr16Bit;
  SerialApp_TxAddr.endPoint = SERIALAPP_ENDPOINT;
  SerialApp_TxAddr.addr.shortAddr = 0x00;   
  
  shortAddr=NLME_GetShortAddr();
  
  strBuf[0] = 0x3B;                          //���͵�ַ��Э���� �����ڵ㲥
  strBuf[1] = HI_UINT16( shortAddr );        //��Ŷ̵�ַ��8λ
  strBuf[2] = LO_UINT16( shortAddr );        //��Ŷ̵�ַ��8λ
  
  osal_memcpy(&strBuf[3], NLME_GetExtAddr(), 8);
  
  if ( AF_DataRequest( &SerialApp_TxAddr, (endPointDesc_t *)&SerialApp_epDesc,
                      SERIALAPP_CLUSTERID,
                      11,
                      strBuf,
                      &SerialApp_MsgID, 
                      0, 
                      AF_DEFAULT_RADIUS ) == afStatus_SUCCESS )
  {
  }
  else
  {
    // Error occurred in request to send.
  }   
}

uint8 XorCheckSum(uint8 * pBuf, uint8 len)
{
  uint8 i;
  uint8 byRet=0;
  
  if(len == 0)
    return byRet;
  else
    byRet = pBuf[0];
  
  for(i = 1; i < len; i ++)
    byRet = byRet ^ pBuf[i];
  
  return byRet;
}

uint8 GetDataLen(uint8 fc)
{
  uint8 len=0;
  switch(fc)
  {
  case 0x07:
  case 0x08:
  case 0x0A:
  case 0x0B:
  case 0x0C:
  case 0x0D:
    len = 1;
    break;
  }
  
  return len;
}

//���P0_5 �̵������ŵĵ�ƽ
uint8 GetLamp( void )
{
  uint8 ret;
  
  if(LAMP_PIN == 0)
    ret = 0;
  else
    ret = 1;
  
  return ret;
}

//���P0_6 MQ-2���崫���������� 0Ϊ�к�����   1Ϊ����
uint8 GetGas( void )
{
  uint8 ret;
  
  if(GAS_PIN == 0)
  {
    ret = 0;
  }
  else
  {
    ret = 1;
  }
  
  return ret;
}
//-------------------------------------------------------------------


//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//#ifdef WSN_BEEP
//���������������
static void MotorData(uchar data)
{
  A1 = 1&(data>>4);
  B1 = 1&(data>>5);
  C1 = 1&(data>>6);
  D1 = 1&(data>>7);
}

//˳ʱ��ת��
static void MotorCW(void)
{
  uchar i;
  for(i=0;i<4;i++)
  {
    MotorData(phasecw[i]);
    Delay_MS(ucSpeed);//ת�ٵ���
  }
}
//��ʱ��ת��
static void MotorCCW(void)
{
  uchar i;
  for(i=0;i<4;i++)
  {
    MotorData(phaseccw[i]);
    Delay_MS(ucSpeed);//ת�ٵ���
  }
}

//ֹͣת��
static void MotorStop(void)
{
  MotorData(0x00);
}

#ifdef WSN_STEP
//��ʼ��IO�ڳ���
static void InitStepMotor(void)
{
  P0SEL &= 0x0F;  //P04 05 06 07����Ϊ��ͨIO
  P0DIR |= 0xF0;  //P04 05 06 07����Ϊ���
  
  MotorData(0x00);//ֹͣת��
}
#endif

static void Delay_MS(unsigned int Time)// 1ms��ʱ
{
  char i;
  
  while(Time--)
  {
    for(i=0;i<100;i++)
      MicroWait(10);
  }
}
//#endif
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


//-------------------------------------------------------------------
//Э��ջ��ʹ��timer 1���PWM��ʹ�õ���������/������ģʽ��ռ�ձȿɵ���
void init_port(void)
{
  P0SEL |= 0x80;         //����P0.7��Ϊ����
  P0DIR |= 0x80;         //����P0.7Ϊ���
  PERCFG |= 0x40;        //���ö�ʱ��1 ��I / O λ��   1�� ����λ��2
  
  return ;
}

// ����׼ֵ����T1CC0 �Ĵ���, �����Ƚ�ֵ����T1CC3�Ĵ���
// ��T1CC3�е�ֵ��T1CC0�е�ֵ���ʱ����T1CC3 ����or���
void init_timer(void)
{
  T1CC0L = 0xff;         //PWM duty cycle  ����
  T1CC0H = 0x0;
  
  T1CC3L = 0x00;        //PWM signal period ռ�ձ�
  T1CC3H = 0x00;
  
  //����T1CC0�е���ֵʱ������ߵ�ƽ 1�� ����T1CC3�е���ֵʱ������͵�ƽ 0 
  //��ʵ����ռ�ձȾ�Ϊ50%  Ϊ�˷�������������������޸���ռ�ձ�
  T1CCTL3 = 0x34;       
  T1CTL |= 0x0f;         // divide with 128 and to do i up-down mode
  return ;
}

void start_pwm(void) 
{
  init_port();
  init_timer();
  // IEN1 |=0x02;     //Timer 1 �ж�ʹ��
  // EA = 1;          //ȫ���ж�ʹ��
  // while(1) {;}
  return ;
}

//volatile unsigned char count = 0;

#pragma vector=T1_VECTOR
__interrupt void _IRQ_timer1(void)
{
  //TODO....
}
//-------------------------------------------------------------------


/*********************************************************************
*********************************************************************/
  