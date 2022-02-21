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
//标准版不同的终端需要修改此ID,用于识别协调器发过来的数据，ID相同则处理
static uint16 EndDeviceID = 0x0001 ; //终端ID，重要
//---------------------------------------------------------------------

//定义节点功能用作传感器或气体+蜂鸣器,还是步进电机
#define WSN_SENSOR     //用作4个采集节点
//#define WSN_BEEP     //气体+蜂鸣器 EndDeviceID=5
//#define WSN_STEP     //步进电机    EndDeviceID=6



#define LAMP_PIN     P0_5  //定义P0.5口为继电器输入端
#define GAS_PIN      P0_6  //定义P0.6口为烟雾传感器的输入端  
#define BEEP_PIN     P0_7  //定义P0.7口为蜂鸣器的输出端  

#define A1 P0_4            //定义步进电机连接端口
#define B1 P0_5
#define C1 P0_6
#define D1 P0_7


#define UART0        0x00
#define MAX_NODE     0x04
#define UART_DEBUG   0x00 //调试宏,通过串口输出协调器和终端的IEEE、短地址
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
uint8 AppTitle[20] = "FHP WSN-system"; //应用程序名称
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

uint8 NodeData[MAX_NODE][5];         //终端数据缓冲区 0=温度 1=湿度 2=气体 3=灯
uint8 TxBuffer[128];

//电机相关的变量
uint8 LedState = 0;
uint8 ucEdDir = 1;      //终端1为正转  2为反转
uint8 ucDirection = 1;  //1为正转  2为反转
uint8 ucSpeed = 2;      //速度2-10之间
uint8 DataBuf[3];

uchar phasecw[4] ={0x80,0x40,0x20,0x10};//正转 电机导通相序 D-C-B-A
uchar phaseccw[4]={0x10,0x20,0x40,0x80};//反转 电机导通相序 A-B-C-D
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
  P0SEL &= ~0x20;         //设置P0.5口为普通IO
  P0DIR |= 0x20;          //设置P0.5为输出
  LAMP_PIN = 1;           //高电平继电器断开;低电平继电器吸合
  P0SEL &= ~0x40;         //设置P0.6为普通IO口
  P0DIR &= ~0x40;         //P0.6定义为输入口
  P0SEL &= ~0x80;         //P0_7配置成通用io
#elif defined WSN_BEEP
  P0SEL &= ~0x40;         //设置P0.6为普通IO口
  P0DIR &= ~0x40;         //P0.6定义为输入口
  start_pwm();            //配置T1输出PWM
  TIMER1_STOP();          //默认关闭蜂鸣器
  EndDeviceID = 0x0005;   //终端5的内部编号  
#elif defined WSN_STEP
  InitStepMotor();        //初始化电机IO引脚
  EndDeviceID = 0x0006;   //终端6的内部编号  
#endif

#if defined(ZDO_COORDINATOR) 
  EndDeviceID = 0x0000; 
#endif
  
  Color    = BLACK; //前景色
  Color_BK = GREEN; //背景色
  osal_memset(AppTitle, 0, 20);
  //LCD上显示应用程序的标题
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
  
  LCD_write_EN_string(64-7*osal_strlen((char *)AppTitle)/2,3,AppTitle); //显示标题
  
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
#if defined(ZDO_COORDINATOR) //协调器通过串口输出自身短地址、IEEE  
          Broadcast_DstAddr.addrMode = (afAddrMode_t)AddrBroadcast;
          Broadcast_DstAddr.endPoint = SERIALAPP_ENDPOINT;
          Broadcast_DstAddr.addr.shortAddr = 0xFFFF;
#if UART_DEBUG           
          PrintAddrInfo( NLME_GetShortAddr(), aExtendedAddress + Z_EXTADDR_LEN - 1);
#endif 
          //初始化灯的状态，1为熄灭状态，0为点亮
          NodeData[0][3] = 1;
          NodeData[1][3] = 1;
          NodeData[2][3] = 1;
          NodeData[3][3] = 1;
#else                        //终端无线发送短地址、IEEE   
          AfSendAddrInfo();
#ifdef WSN_BEEP              //蜂鸣器和气体实验时自动检测气体发现异常就报警
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
  
  //在此事件中可以定时向协调器发送节点传感器参数信息
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
  if ( keys & HAL_KEY_SW_6 ) //按S1键启动或停止终端定时上报数据 
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
  
  if ( keys & HAL_KEY_SW_1 ) //按S2
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
  
  //查询单个终端上所有传感器的数据 3A 00 01 02 39 23  响应：3A 00 01 02 00 00 00 00 xor 23
  switch ( pkt->clusterId )
  {
    // A message with a serial data block to be transmitted on the serial port.
  case SERIALAPP_CLUSTERID:
    osal_memcpy(afRxData, pkt->cmd.Data, pkt->cmd.DataLength);
    switch(afRxData[0]) //简单协议命令字解析
    {
#if defined(ZDO_COORDINATOR)
    case 0x3B:  //收到终端无线发过来的短地址和IEEE地址,通过串口输出显示      
      shortAddr=(afRxData[1]<<8)|afRxData[2];
      pIeeeAddr = &afRxData[3];
#if UART_DEBUG
      PrintAddrInfo(shortAddr, pIeeeAddr + Z_EXTADDR_LEN - 1);
#endif   
      break;
    case 0x3A:	
      if(afRxData[3] == 0x02) //收到终端传过来的传感器数据并保存
      {  
        NodeData[afRxData[2]-1][0] = afRxData[4];
        NodeData[afRxData[2]-1][1] = afRxData[5];
        NodeData[afRxData[2]-1][2] = afRxData[6];
        NodeData[afRxData[2]-1][3] = afRxData[7];
        NodeData[afRxData[2]-1][4] = 0x00;
      }
      
#if UART_DEBUG
      HalUARTWrite (UART0, NodeData[afRxData[3]-1], 4); //调试时通过串口输出
      HalUARTWrite (UART0, "\n", 1);
#endif            
      break;
#else  
    case 0x3A:  //开关灯设备          
      if(afRxData[3] == 0x0A || afRxData[3] == 0x0B || afRxData[3] == 0x0C) //控制终端          
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
      else if(afRxData[3] == 0x07)      //蜂鸣器 功能码为07
      {
        if(EndDeviceID == afRxData[2] || afRxData[2] == 0xFF)  //蜂鸣器 EndDeviceID为05
        {
          if(afRxData[4] == 0)
          {
            TIMER1_STOP();               //收到协调发出的蜂鸣器不响的指令
            HalLedSet ( HAL_LED_2, HAL_LED_MODE_OFF );
          }
          else
          {
            TIMER1_RUN();               //收到协调发出的蜂鸣器响的指令
            HalLedSet ( HAL_LED_2, HAL_LED_MODE_ON );
          }
        } 
      }
      else if(afRxData[3] == 0x08)    //电机 功能码为08
      {
        if(EndDeviceID == afRxData[2] || afRxData[2] == 0xFF)//电机 EndDeviceID为06
        {
          ucEdDir = afRxData[4];      //保存旋转方向给调速用
          MotorStop();                //停止转动
          if(afRxData[4] == 0x02)   
          {
            for(i=0;i<2000;i++)
              MotorCW();              //顺时针转动
          }
          else if(afRxData[4] == 0x01)//左转标记 
          {
            for(i=0;i<2000;i++)
              MotorCCW();             //逆时针转动
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
  case 0x01: //查询所有终端传感器的数据
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
  case 0x02: //查询单个终端上所有传感器的数据
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

        //接收数据正确返回相应数据
        if(checksum == SerialApp_TxBuf[len] && SerialApp_TxBuf[len+1] == 0x23)
        {
          if(FC == 7 || FC == 8 || FC == 0x0A || FC == 0x0B || FC == 0x0C) //控制终端
          {                            
            if (afStatus_SUCCESS == AF_DataRequest(&Broadcast_DstAddr,
                                                   (endPointDesc_t *)&SerialApp_epDesc,
                                                   SERIALAPP_CLUSTERID,
                                                   len+2, SerialApp_TxBuf,
                                                   &SerialApp_MsgID, 0, AF_DEFAULT_RADIUS))
            {
              if(FC == 0x0A) //如果开启自动刷新则不需要这步操作
                NodeData[addr-1][3] = SerialApp_TxBuf[len-1];  //更新缓冲区灯的状态
              
              HalUARTWrite(UART0, SerialApp_TxBuf, len+2); //无线发送成功后原样返回给上位机	
              //osal_set_event(SerialApp_TaskID, SERIALAPP_SEND_EVT);
            }
            else  //暂时没发现错误，关闭终端发送也正常。无线发送失败后将数据位和校验位置0返给上位机	
            {
              SerialApp_TxBuf[len-1] = 0x00;
              SerialApp_TxBuf[len] = 0x00;
              HalUARTWrite(UART0, SerialApp_TxBuf, len+2);
            }
          }
          else
          {
            SendData(addr, FC);   //查询操作
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
//查询单个终端上所有传感器的数据 3A 00 01 02 XX 23  响应：3A 00 01 02 00 00 00 00 xor 23
void SerialApp_SendPeriodicMessage( void )
{
  uint8 SendBuf[11]={0};

#ifdef WSN_SENSOR  
  SendBuf[0] = 0x3A;                          
  SendBuf[1] = HI_UINT16( EndDeviceID );
  SendBuf[2] = LO_UINT16( EndDeviceID );
  SendBuf[3] = 0x02;                       //FC
  
  DHT11();                //获取温湿度
  SendBuf[4] = wendu;  
  SendBuf[5] = shidu;  
  SendBuf[6] = GetGas();  //获取气体传感器的状态  
  SendBuf[7] = GetLamp(); //获得灯的状态
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
  SendBuf[0] = GetGas();  //获取气体传感器的状态 0为有害气体   1为正常
  
  //终端5执行蜂鸣器操作   蜂鸣器动作电平 1: 响 ，0: 不响
  if(SendBuf[0] == 0 && EndDeviceID == 5)
  {
    TIMER1_RUN();      //检测到异常气体时蜂鸣器响
  }
  else
  {
    TIMER1_STOP();    //气体正常不响
  }    
#endif
}


#if UART_DEBUG   
//通过串口输出短地址 IEEE
void PrintAddrInfo(uint16 shortAddr, uint8 *pIeeeAddr)
{
  uint8 strIeeeAddr[17] = {0};
  char  buff[30] = {0};    
  
  //获得短地址   
  sprintf(buff, "shortAddr:%04X   IEEE:", shortAddr);  
  
  //获得IEEE地址
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
  
  strBuf[0] = 0x3B;                          //发送地址给协调器 可用于点播
  strBuf[1] = HI_UINT16( shortAddr );        //存放短地址高8位
  strBuf[2] = LO_UINT16( shortAddr );        //存放短地址低8位
  
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

//获得P0_5 继电器引脚的电平
uint8 GetLamp( void )
{
  uint8 ret;
  
  if(LAMP_PIN == 0)
    ret = 0;
  else
    ret = 1;
  
  return ret;
}

//获得P0_6 MQ-2气体传感器的数据 0为有害气体   1为正常
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
//步进电机驱动部分
static void MotorData(uchar data)
{
  A1 = 1&(data>>4);
  B1 = 1&(data>>5);
  C1 = 1&(data>>6);
  D1 = 1&(data>>7);
}

//顺时针转动
static void MotorCW(void)
{
  uchar i;
  for(i=0;i<4;i++)
  {
    MotorData(phasecw[i]);
    Delay_MS(ucSpeed);//转速调节
  }
}
//逆时针转动
static void MotorCCW(void)
{
  uchar i;
  for(i=0;i<4;i++)
  {
    MotorData(phaseccw[i]);
    Delay_MS(ucSpeed);//转速调节
  }
}

//停止转动
static void MotorStop(void)
{
  MotorData(0x00);
}

#ifdef WSN_STEP
//初始化IO口程序
static void InitStepMotor(void)
{
  P0SEL &= 0x0F;  //P04 05 06 07定义为普通IO
  P0DIR |= 0xF0;  //P04 05 06 07定义为输出
  
  MotorData(0x00);//停止转动
}
#endif

static void Delay_MS(unsigned int Time)// 1ms延时
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
//协议栈里使用timer 1输出PWM，使用的是正计数/倒计数模式，占空比可调整
void init_port(void)
{
  P0SEL |= 0x80;         //设置P0.7口为外设
  P0DIR |= 0x80;         //设置P0.7为输出
  PERCFG |= 0x40;        //设置定时器1 的I / O 位置   1： 备用位置2
  
  return ;
}

// 将基准值放入T1CC0 寄存器, 将被比较值放入T1CC3寄存器
// 当T1CC3中的值与T1CC0中的值相等时，则T1CC3 设置or清除
void init_timer(void)
{
  T1CC0L = 0xff;         //PWM duty cycle  周期
  T1CC0H = 0x0;
  
  T1CC3L = 0x00;        //PWM signal period 占空比
  T1CC3H = 0x00;
  
  //等于T1CC0中的数值时候，输出高电平 1； 等于T1CC3中的数值时候，输出低电平 0 
  //其实整个占空比就为50%  为了蜂鸣器输出连续的响声修改了占空比
  T1CCTL3 = 0x34;       
  T1CTL |= 0x0f;         // divide with 128 and to do i up-down mode
  return ;
}

void start_pwm(void) 
{
  init_port();
  init_timer();
  // IEN1 |=0x02;     //Timer 1 中断使能
  // EA = 1;          //全局中断使能
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
  