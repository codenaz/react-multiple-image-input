import React from 'react';
import styled, { css } from 'styled-components';
import PropTypes from 'prop-types';
import Text from './Text';

const Content = styled.div`
  background-color: ${({ theme }) => theme.colors.modalColor};
  border-radius: 5px;
  max-width: 360px;
  transition: transform 0.3s ease-out;
  z-index: 9999;
`;

const Overlay = styled.div`
  background-color: rgba(0, 0, 0, 0.8);
  bottom: 0;
  dsplay: flex;
  left: 0;
  opacity: 0;
  position: fixed;
  right: 0;
  top: 0;
  transition: all 0.3s;
`;

const Wrapper = styled.div`
  align-items: center;
  bottom: 0;
  dsplay: flex;
  justify-content: center;
  left: 0;
  opacity: 0;
  pointer-events: none;
  position: fixed;
  right: 0;
  top: 0;
  transition: all 0.3s;
  visibility: hidden;
  z-index: 9;

  ${Content} {
    transform: translate(0, -50px);
  }

  ${({ isOpen }) =>
    isOpen &&
    css`
      display: flex;
      opacity: 1;
      pointer-events: auto;
      visibility: visible;

      ${Content} {
        transform: translate(0, 0);
      }

      ${Overlay} {
        opacity: 1;
      }
    `}
`;

const HeaderWrapper = styled.div`
  align-items: center;
  border-bottom: 1px solid ${({ theme }) => theme.colors.outlineColor};
  display: flex;
  justify-content: center;
  padding: 20px;
`;

const Body = styled.div`
  padding: 15px;
  position: relative;
`;

const Footer = styled.div`
  display: flex;
  justify-content: center;
  padding: 0 15px 15px 15px;
`;

const Header = ({ children, ...props }) => {
  return (
    <HeaderWrapper {...props}>
      <Text align="center">{children}</Text>
    </HeaderWrapper>
  );
};

const Modal = ({ children, isOpen, toggle }) => (
  <Wrapper isOpen={isOpen}>
    <Overlay onClick={toggle} />
    <Content>{children}</Content>
  </Wrapper>
);

Modal.Header = Header;
Modal.Body = Body;
Modal.Footer = Footer;

Modal.propTypes = {
  children: PropTypes.node.isRequired,
  isOpen: PropTypes.bool.isRequired,
  toggle: PropTypes.func.isRequired
};

export default Modal;
