import styled from 'styled-components';

const Text = styled.span`
  &,
  &:visited {
    color: ${props => props.theme.colors[props.color]};
  }
  display: inline-block;
  font-family: inherit;
  font-size: ${props => props.theme.font.size[props.fontSize]};
  font-weight: ${props => props.theme.font.weight[props.fontWeight]};
  line-height: ${props =>
    props.caption ? props.theme.font.size.small : props.theme.font.size.normal};
  text-align: ${props => props.theme.font.align[props.textAlign]};
`;

Text.defaultProps = {
  color: 'textColor',
  fontWeight: 'normal'
};

export default Text;
