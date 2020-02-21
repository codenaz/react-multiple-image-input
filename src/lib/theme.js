const theme = {
  buttons: {
    small: {
      fontSize: '1.2rem',
      fontWeight: 'normal',
      padding: '0.5rem 1.0rem'
    },
    normal: {
      fontSize: '1.4rem',
      fontWeight: 'normal',
      height: '4.0rem',
      padding: '0.5rem 1.0rem'
    },
    large: {
      fontSize: '1.4rem',
      fontWeight: 'bold',
      height: '5.0rem',
      padding: '1.4rem 3.0rem'
    }
  },
  font: {
    align: {
      center: 'center',
      initial: 'initial',
      left: 'left',
      right: 'right'
    },
    size: {
      big: '1.8rem',
      inherit: 'inherit',
      normal: '1.6rem',
      small: '1.4rem'
    },
    weight: {
      normal: 'normal',
      medium: 'medium',
      bold: 'bold'
    }
  }
};

const darkTheme = {
  colors: {
    background: '#111111',
    outlineColor: 'rgba(255,255,255,0.6)',
    textColor: 'rgba(255,255,255,0.6)',
    buttonColor: '#ff0e1f'
  }
};

const lightTheme = {
  colors: {
    background: '#ffffff',
    outlineColor: '#111111',
    textColor: 'rgba(255,255,255,0.6)',
    buttonColor: '#ff0e1f'
  }
};

export { darkTheme, lightTheme };

export default theme;
